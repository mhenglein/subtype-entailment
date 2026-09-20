"""Behavioral tests for the unverified boundary around the checked algorithm."""
import contextlib
import io
import itertools
import json
from pathlib import Path
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

import subtail as cli


class SubtailTests(unittest.TestCase):
    def problem(self, query=None, constraints=None):
        return cli.parse_problem({'variables': ['x', 'y'],
                                  'constraints': constraints or [],
                                  'query': query or ['x', 'y']})

    def test_parser_does_not_emit_names_as_code(self):
        name = 'x); #eval IO.println "bad" --'
        p = cli.parse_problem({'variables': [name], 'constraints': [], 'query': [name, 'bottom']})
        source = cli.lean_source(p)
        self.assertNotIn(name, source)
        self.assertIn('Expr 1', source)
        self.assertIn('(.var 0)', source)

    def test_parser_rejects_invalid_syntax(self):
        base = {'variables': ['x'], 'constraints': [], 'query': ['x', 'bottom']}
        for change in [dict(variables=['x','x']), dict(variables=['bottom']),
                       dict(query=['top','x']), dict(query=[{'prod':['x']},'x']),
                       dict(query=[{'var':0},'x']), dict(constraints='x'),
                       dict(extra=1)]:
            with self.subTest(change=change), self.assertRaises(ValueError):
                cli.parse_problem({**base, **change})

    def test_zero_variables_and_nested_products(self):
        p = cli.parse_problem({'variables': [], 'constraints': [],
                              'query': [{'prod':['bottom','bottom']}, 'bottom']})
        self.assertEqual(p.query[0], ('prod', ('bot',), ('bot',)))
        self.assertIn('Expr 0', cli.lean_source(p))

    def test_true_root_counterexample_is_not_missing_path(self):
        p = self.problem()
        report = cli.check_countermodel(p, {'nodes':[None,[0,0]], 'roots':{'x':1,'y':0}})
        self.assertTrue(report['valid'])
        self.assertEqual(report['separating_path'], [])

    def test_reject_failed_premise_and_satisfied_query(self):
        model = {'nodes':[None,[0,0]], 'roots':{'x':1,'y':0}}
        bad = cli.check_countermodel(self.problem(constraints=[['x','y']]), model)
        self.assertEqual(bad['reason'], 'premise_fails')
        good_query = cli.check_countermodel(self.problem(query=['y','x']), model)
        self.assertEqual(good_query['reason'], 'query_holds')

    def test_regular_infinite_zero_spine(self):
        p = cli.parse_problem({'variables':['x'],
                              'constraints':[[{'prod':['x','bottom']},'x']],
                              'query':['x','bottom']})
        self.assertTrue(cli.check_countermodel(p, {'nodes':[None,[1,0]], 'roots':{'x':1}})['valid'])
        self.assertEqual(cli.separating_path([None,(1,0)],1,1), None)
        # Same roots with a finite root-only tree violate the recursive premise.
        self.assertFalse(cli.check_countermodel(p, {'nodes':[None,[0,0]], 'roots':{'x':1}})['valid'])

    def test_nonempty_address(self):
        # x has a left product child; y only has its root product.
        p = self.problem()
        report = cli.check_countermodel(p, {'nodes':[None,[0,0],[1,0]],'roots':{'x':2,'y':1}})
        self.assertTrue(report['valid'])
        self.assertEqual(report['separating_path'], [0])

    def test_invalid_graph_rejected(self):
        for nodes in [[], [True], [[0,2]], [[True,0]], [['top',0]]]:
            with self.subTest(nodes=nodes), self.assertRaises(ValueError):
                cli.check_countermodel(self.problem(), {'nodes':nodes,'roots':{'x':0,'y':0}})

    def test_independent_finite_address_crosscheck(self):
        def trees(depth):
            if depth == 0: return [None]
            smaller = trees(depth-1)
            return [None] + list(itertools.product(smaller, repeat=2))
        def addresses(t):
            if t is None: return set()
            return {()} | {(0,)+p for p in addresses(t[0])} | {(1,)+p for p in addresses(t[1])}
        def encode(t, nodes):
            if t is None: return 0
            left, right = encode(t[0], nodes), encode(t[1], nodes)
            nodes.append((left,right));return len(nodes)-1
        ts = trees(3)
        self.assertEqual(len(ts),26)
        for a, b in itertools.product(ts, repeat=2):
            nodes=[None];left=encode(a,nodes);right=encode(b,nodes)
            path=cli.separating_path(nodes,left,right)
            difference=addresses(a)-addresses(b)
            self.assertEqual(path is None, not difference)
            if path is not None:self.assertIn(tuple(path),difference)

    def test_no_model_is_unknown_not_entailment(self):
        report = cli.find_countermodel(self.problem(query=['x','x']), time.monotonic()+1, max_models=3)
        self.assertEqual(report['status'], 'UNKNOWN')
        self.assertEqual(report['candidates'], 3)

    def test_certificate_timeout(self):
        with self.assertRaises(TimeoutError):
            cli.check_countermodel(self.problem(), {'nodes':[None,[0,0]],'roots':{'x':1,'y':0}},0)

    def test_process_timeout_reaps_child(self):
        result=cli.run_process([sys.executable,'-c','import time;time.sleep(10)'], cli.ROOT, .05)
        self.assertEqual(result['status'],'UNKNOWN')
        self.assertEqual(result['reason'],'time_limit')

    def test_failed_and_missing_tool_are_unknown(self):
        failed=cli.run_process([sys.executable,'-c','raise SystemExit(7)'],cli.ROOT,3)
        self.assertEqual(failed['status'],'UNKNOWN')
        missing=cli.run_process(['/nonexistent/subtail-test-command'],cli.ROOT,1)
        self.assertEqual(missing['status'],'UNKNOWN')

    def test_marker_does_not_override_failed_process(self):
        with patch.object(cli,'run_process',side_effect=[{'status':'PASS','seconds':0},
             {'status':'UNKNOWN','reason':'process_failed_or_resource_limit','output':cli.MARKER+'true'}]):
            result=cli.run_native(self.problem(),time.monotonic()+1)
            self.assertEqual(result['status'],'UNKNOWN')

    def test_certificate_mode_reports_its_own_trust_boundary(self):
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            code = cli.main([str(cli.ROOT/'examples/entailment/zero-spine.json'),
                             '--check-model', str(cli.ROOT/'examples/entailment/zero-spine-model.json')])
        report = json.loads(output.getvalue())
        self.assertEqual(code, 0)
        self.assertIn('Lean was not run', report['trust_boundary'])

    def test_ambiguous_marker_is_unknown(self):
        with patch.object(cli,'run_process',side_effect=[{'status':'PASS','seconds':0},
             {'status':'PASS','seconds':0,'output':cli.MARKER+'true\n'+cli.MARKER+'false'}]):
            result=cli.run_native(self.problem(),time.monotonic()+1)
            self.assertEqual(result['status'],'UNKNOWN')


if __name__ == '__main__':
    unittest.main()
