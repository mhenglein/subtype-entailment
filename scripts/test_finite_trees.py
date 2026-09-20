"""Independent finite-state and bounded-model checks for the finite-tree route."""
from itertools import product
import contextlib
import io
import json
import random
import time
import unittest
from unittest.mock import patch

import finite_trees as finite
import regular_countermodel as regular
import subtail


from experiments.check_finite_trees import threshold_hot


class FiniteTreeTests(unittest.TestCase):
    def test_hot_matches_independent_length_threshold(self):
        rng = random.Random(5801)
        for _ in range(160):
            n = rng.randrange(1,4)
            eps = {(p,q) for p in range(n) for q in range(n) if rng.random()<.2}
            push = {(p,a,q) for p in range(n) for a in (0,1) for q in range(n) if rng.random()<.15}
            pop = {(p,a,q) for p in range(n) for a in (0,1) for q in range(n) if rng.random()<.15}
            system = regular.System(n,eps,push,pop,{q for _,_,q in push},set(),0,0)
            actual = finite.growth_analysis(system)
            self.assertEqual(set(actual['hot']), threshold_hot(system))
            if actual['cycle']:
                c = actual['cycle']
                self.assertTrue(c['forced_root'])
                self.assertTrue(c['word'])
                reverse = regular.PopMachine(system.reverse())
                for k in (1,2,3,8):
                    self.assertTrue(reverse.run(c['control'], c['word']*k) & (1<<c['control']))

    def test_epsilon_and_balanced_cycles_are_not_growth(self):
        epsilon = regular.System(2,{(0,1),(1,0)},set(),set(),set(),set(),0,1)
        self.assertEqual(finite.growth_analysis(epsilon)['hot'],[])
        balanced = regular.System(2,set(),{(0,0,1)},{(1,0,0)},{1},set(),0,1)
        self.assertEqual(finite.growth_analysis(balanced)['hot'],[])

    def test_zero_spine_obstructs_every_finite_model(self):
        p = subtail.parse_problem({'variables':['x'],
            'constraints':[[{'prod':['x','bottom']},'x']], 'query':['x','bottom']})
        self.assertTrue(finite.analyze_problem(p)['finite_model_obstruction'])
        graph = {'nodes':[None,[1,0]],'roots':{'x':1}}
        self.assertTrue(subtail.check_countermodel(p, graph)['valid'])
        self.assertIsNone(finite.finite_graph_height(graph['nodes'], graph['roots'].values()))

    def test_nonempty_system_can_have_finite_and_infinite_models(self):
        p = subtail.parse_problem({'variables':['x','y'], 'constraints':[['x','y']], 'query':['y','x']})
        self.assertFalse(finite.analyze_problem(p)['finite_model_obstruction'])
        self.assertTrue(subtail.check_countermodel(p,{'nodes':[None,[1,1]],'roots':{'x':0,'y':1}})['valid'])
        model=regular.extract(p,max_words=4)['model']
        self.assertIsNotNone(finite.finite_graph_height(model['nodes'],model['roots'].values()))

    def test_only_reachable_cycles_matter_for_graph_finiteness(self):
        nodes=[None,[0,0],[1,1],[3,3]]
        self.assertEqual(finite.finite_graph_height(nodes,[2]),2)
        self.assertEqual(finite.finite_graph_height(nodes,iter([2])),2)
        self.assertIsNone(finite.finite_graph_height(nodes,[3]))
        self.assertEqual(finite.finite_graph_height(nodes,[]),0)

    def test_cold_closures_have_bounded_depth(self):
        rng=random.Random(5802)
        for _ in range(100):
            n=3
            eps={(p,q) for p in range(n) for q in range(n) if rng.random()<.12}
            push={(p,a,q) for p in range(n) for a in (0,1) for q in range(n) if rng.random()<.09}
            pop={(p,a,q) for p in range(n) for a in (0,1) for q in range(n) if rng.random()<.09}
            system=regular.System(n,eps,push,pop,{q for _,_,q in push},set(),0,1)
            if finite.growth_analysis(system)['hot']:
                continue
            word=(0,1,0)
            seeds={(q,()) for q in system.forced}|{(0,word[:i]) for i in range(len(word)+1)}
            nfa=regular.ClosureNFA(regular.PopMachine(system),regular.PopMachine(system.reverse()),seeds)
            graph=nfa.graph(tuple(range(n)))
            height=finite.finite_graph_height(graph['nodes'],graph['roots'].values())
            self.assertIsNotNone(height)
            self.assertLessEqual(height,len(word)+n)

    def test_unforced_push_system_does_not_claim_a_model_obstruction(self):
        system=regular.System(1,set(),{(0,0,0)},set(),set(),set(),0,0)
        result=finite.growth_analysis(system)
        self.assertTrue(result['has_consuming_cycle'])
        self.assertFalse(result['cycle']['forced_root'])
        self.assertNotIn('finite_model_obstruction',result)

    def test_finite_native_requires_both_result_markers(self):
        p=subtail.parse_problem({'variables':[], 'constraints':[], 'query':['bottom','bottom']})
        for text in (subtail.MARKER+'true',
                     subtail.GROWTH_MARKER+'true\n'+subtail.MARKER+'false',
                     subtail.GROWTH_MARKER+'false\n'+subtail.GROWTH_MARKER+'false\n'+subtail.MARKER+'true'):
            with self.subTest(text=text), patch.object(subtail,'run_process',side_effect=[
                {'status':'PASS','seconds':0}, {'status':'PASS','seconds':0,'output':text}]):
                self.assertEqual(subtail.run_native(p,time.monotonic()+1,finite_trees=True)['status'],'UNKNOWN')

    def test_finite_process_failure_cannot_supply_a_decision(self):
        p=subtail.parse_problem({'variables':[], 'constraints':[], 'query':['bottom','bottom']})
        with patch.object(subtail,'run_process',side_effect=[{'status':'PASS','seconds':0},
             {'status':'UNKNOWN','reason':'time_limit','output':subtail.GROWTH_MARKER+'true\n'+subtail.MARKER+'true'}]):
            self.assertEqual(subtail.run_native(p,time.monotonic()+1,finite_trees=True)['status'],'UNKNOWN')

    def test_finite_source_calls_checked_procedure(self):
        name='x); #eval IO.println "bad" --'
        p=subtail.parse_problem({'variables':[name], 'constraints':[], 'query':[name,'bottom']})
        source=subtail.lean_source(p,finite_trees=True)
        self.assertNotIn(name,source)
        self.assertIn('Subtail.FiniteTreeDecision.run input left right',source)
        self.assertIn('toString answer.2',source)

    def test_finite_cli_rejects_infinite_graph(self):
        output=io.StringIO()
        with contextlib.redirect_stdout(output):
            code=subtail.main([str(subtail.ROOT/'examples/entailment/zero-spine.json'),
                '--finite-trees','--check-model',str(subtail.ROOT/'examples/entailment/zero-spine-model.json')])
        result=json.loads(output.getvalue())
        self.assertEqual(code,1)
        self.assertEqual(result['status'],'INVALID_MODEL')
        self.assertEqual(result['countermodel']['reason'],'infinite_variable_tree')

    def test_finite_cli_uses_native_growth_and_reports_its_boundary(self):
        output=io.StringIO()
        with patch.object(finite,'analyze_problem',side_effect=AssertionError('Python gate called')), \
             patch.object(subtail,'run_process',side_effect=[{'status':'PASS','seconds':0},
                {'status':'PASS','seconds':0,'output':subtail.GROWTH_MARKER+'true\n'+subtail.MARKER+'true'}]), \
             contextlib.redirect_stdout(output):
            code=subtail.main([str(subtail.ROOT/'examples/entailment/zero-spine.json'),'--finite-trees'])
        result=json.loads(output.getvalue())
        self.assertEqual(code,0)
        self.assertEqual(result['status'],'ENTAILED')
        self.assertEqual(result['reason'],'no_finite_model')
        self.assertEqual(result['basis'],'Lean FiniteTreeDecision.entailsCheck_correct')
        self.assertIn('unconditional correctness proofs',result['trust_boundary'])

    def test_finite_cli_rechecks_extracted_graph(self):
        output=io.StringIO()
        with patch.object(subtail,'run_native',return_value={'status':'NOT_ENTAILED'}), \
             patch.object(subtail,'find_countermodel',return_value={'status':'FOUND',
                'countermodel':{'valid':True,'nodes':[None,[1,0]],'roots':{'x':1}}}), \
             contextlib.redirect_stdout(output):
            code=subtail.main([str(subtail.ROOT/'examples/entailment/zero-spine.json'),'--finite-trees'])
        result=json.loads(output.getvalue())
        self.assertEqual(code,0)
        self.assertEqual(result['status'],'NOT_ENTAILED')
        self.assertNotIn('countermodel',result)
        self.assertEqual(result['explanation_search']['status'],'UNKNOWN')


if __name__=='__main__':
    unittest.main()
