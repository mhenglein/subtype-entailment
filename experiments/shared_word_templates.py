"""Shared-word relation composition and universal witness-family validation.

The compiler uses ONLY word equations and regular-language membership.  With
an exact decision procedure for that theory, every supplied family's universal
validity is decidable for ANY binary BorderAvoid instance.  This is NOT a
procedure deciding whether an arbitrary mixed family contains a witness.

The optional native Z3 runner is a resource-bounded, incomplete implementation
backend.  It may return UNKNOWN.  Satisfying models are checked independently;
UNSAT results retain the stated solver trust boundary, not a Lean certificate.
"""
from dataclasses import dataclass, replace
from functools import lru_cache
from pathlib import Path
import json
import re
import subprocess
import sys
from typing import Tuple

from border_lab import Instance, witness, border_witness

# Small immutable regular-expression language; None denotes the empty language.
EPS = ('lit', '')
ZERO = ('lit', '0')
ONE = ('lit', '1')

def lit(s):
    if not isinstance(s, str) or any(c not in '01' for c in s):
        raise ValueError('Only binary constants are permitted')
    return ('lit', s)

def alt(*xs):
    flat = set()
    for x in xs:
        if x is not None:
            flat.update(x[1:] if x[0] == 'alt' else (x,))
    if not flat:
        return None
    seq = tuple(sorted(flat, key=repr))
    return seq[0] if len(seq) == 1 else ('alt',) + seq

def cat(*xs):
    flat = []
    for x in xs:
        if x is None:
            return None
        if x == EPS:
            continue
        flat.extend(x[1:] if x[0] == 'cat' else (x,))
    if not flat:
        return EPS
    return flat[0] if len(flat) == 1 else ('cat',) + tuple(flat)

def star(x):
    if x is None or x == EPS:
        return EPS
    return x if x[0] == 'star' else ('star', x)

BINARY = star(alt(ZERO, ONE))

@lru_cache(maxsize=None)
def regex_python(x):
    if x is None:
        return '(?!)'
    op = x[0]
    if op == 'lit':
        return re.escape(x[1])
    if op == 'alt':
        return '(?:' + '|'.join(regex_python(t) for t in x[1:]) + ')'
    if op == 'cat':
        return ''.join(regex_python(t) for t in x[1:])
    if op == 'star':
        return '(?:' + regex_python(x[1]) + ')*'
    raise ValueError('Unsupported regular-expression operator')

@lru_cache(maxsize=None)
def regex_smt(x):
    if x is None:
        return '(as re.none (RegEx String))'
    op = x[0]
    if op == 'lit':
        return '(str.to_re ' + json.dumps(x[1]) + ')'
    name = {'alt':'re.union', 'cat':'re.++', 'star':'re.*'}[op]
    return '(' + name + ' ' + ' '.join(regex_smt(y) for y in x[1:]) + ')'

def regex_accepts(x, s):
    return bool(re.fullmatch(regex_python(x), s))

@dataclass(frozen=True)
class Var:
    name: str
    def __post_init__(self):
        if not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', self.name):
            raise ValueError('Variable names must be plain identifiers')


def expr(*terms):
    out = []
    for t in terms:
        if isinstance(t, tuple):
            out.extend(t)
        elif isinstance(t, (str, Var)):
            if isinstance(t, str):
                lit(t)
            out.append(t)
        else:
            raise ValueError('Expressions contain only constants and Var objects')
    return tuple(out)

def evaluate(e, assignment):
    return ''.join(assignment[t.name] if isinstance(t, Var) else t for t in e)

def smt_expr(e):
    terms = [t.name if isinstance(t, Var) else json.dumps(t) for t in e]
    return '""' if not terms else terms[0] if len(terms)==1 else '(str.++ ' + ' '.join(terms) + ')'

@dataclass(frozen=True)
class Relation:
    # Every variable is existentially assigned, including output-only variables.
    domains: Tuple[Tuple[str, object], ...]
    inputs: Tuple[Tuple[object, ...], ...]
    outputs: Tuple[Tuple[object, ...], ...]
    equations: Tuple[Tuple[Tuple[object, ...], Tuple[object, ...]], ...] = ()

    def __post_init__(self):
        names = [v for v, _ in self.domains]
        if len(set(names)) != len(names):
            raise ValueError('Duplicate variables')
        for name, language in self.domains:
            Var(name); regex_smt(language)
        for e in self.inputs + self.outputs + tuple(t for eq in self.equations for t in eq):
            for t in e:
                if isinstance(t, Var):
                    if t.name not in names:
                        raise ValueError('Undeclared variable: ' + t.name)
                else:
                    lit(t)

    def satisfies(self, assignment):
        return all(n in assignment and regex_accepts(r, assignment[n]) for n,r in self.domains) \
            and all(evaluate(a,assignment)==evaluate(b,assignment) for a,b in self.equations)


def rename(R, prefix):
    def e(xs):
        return tuple(Var(prefix+t.name) if isinstance(t,Var) else t for t in xs)
    return Relation(tuple((prefix+n,r) for n,r in R.domains),
                    tuple(e(x) for x in R.inputs), tuple(e(x) for x in R.outputs),
                    tuple((e(a),e(b)) for a,b in R.equations))


def compose(left, right):
    """Exact existential relational composition, retaining all interface equalities.

    Alpha-renaming prevents accidental capture.  No implication that an
    unbounded sequence of such compositions admits a finite saturation.
    """
    if len(left.outputs) != len(right.inputs):
        raise ValueError('Interface arities differ')
    L, R = rename(left,'l_'), rename(right,'r_')
    return Relation(L.domains+R.domains, L.inputs, R.outputs,
                    L.equations+R.equations+tuple(zip(L.outputs,R.inputs)))

@lru_cache(maxsize=None)
def path_regex(delta, start, final):
    """Exact GNFA state elimination for a partial binary transition table."""
    n = len(delta)
    if not 0 <= start < n or any(not 0 <= q < n for q in final):
        raise ValueError('Invalid endpoint')
    # Trim first, without affecting epsilon paths.
    reach = {start}; todo = [start]
    for p in todo:
        for q in delta[p]:
            if q >= 0 and q not in reach:
                reach.add(q); todo.append(q)
    reverse = {q: [] for q in range(n)}
    for p,row in enumerate(delta):
        for q in row:
            if q >= 0:
                reverse[q].append(p)
    co=set(final); todo=list(co)
    for q in todo:
        for p in reverse[q]:
            if p not in co:
                co.add(p); todo.append(p)
    live=reach & co
    if start not in live:
        return None
    S,T=n,n+1
    edges={(S,start):EPS}
    for q in final:
        if q in live:
            edges[q,T]=EPS
    for p in sorted(live):
        for a,q in enumerate(delta[p]):
            if q in live:
                edges[p,q]=alt(edges.get((p,q)),lit(str(a)))
    remaining=set(live)
    while remaining:
        def score(q):
            ins=[x for (p,t),x in edges.items() if t==q and p!=q]
            outs=[x for (p,t),x in edges.items() if p==q and t!=q]
            return (len(ins)*len(outs), sum(len(repr(x)) for x in ins+outs),q)
        q=min(remaining,key=score)
        ins=[(p,x) for (p,t),x in list(edges.items()) if t==q and p!=q]
        outs=[(t,x) for (p,t),x in list(edges.items()) if p==q and t!=q]
        loop=star(edges.get((q,q)))
        for p,x in ins:
            for t,y in outs:
                edges[p,t]=alt(edges.get((p,t)),cat(x,loop,y))
        edges={pair:x for pair,x in edges.items() if q not in pair}
        remaining.remove(q)
    return edges.get((S,T))


def admissible_regex(I):
    table=tuple(tuple(q if p not in I.bad and q not in I.bad else -1 for q in row)
                for p,row in enumerate(I.delta))
    return path_regex(table,I.start,tuple(sorted(I.final-I.bad))) if I.start not in I.bad else None


def validate_instance(I):
    k=len(I.delta)
    if I.alphabet!='01' or not k or not 0<=I.start<k:
        raise ValueError('A nonempty binary instance is required')
    if any(len(row)!=2 or any(type(q) is not int or not -1<=q<k for q in row) for row in I.delta):
        raise ValueError('Malformed transitions')
    if any(not 0<=q<k for q in I.final|I.bad):
        raise ValueError('Malformed annotations')
    if any(len(p)!=2 or any(not 0<=q<k for q in p) for p in I.flags):
        raise ValueError('Malformed flags')


def family_script(I,R,word_expression,mode='bad',timeout_ms=5000,engine='seq'):
    """Generate existential equations/regular constraints, no length predicates.

    mode='bad' asks for ONE instantiation that is NOT a witness.
    mode='base' asks for any instantiation. No unrestricted nonexistence
    conclusion follows from absence of a bad instantiation.
    """
    validate_instance(I)
    if mode not in ('base','bad') or engine not in ('seq','z3str3'):
        raise ValueError('Unsupported mode or engine')
    if type(timeout_ms) is not int or timeout_ms<1:
        raise ValueError('timeout_ms must be positive')
    # Name all template variables hygienically, preserving shared occurrences.
    subst={n:'v_'+n for n,_ in R.domains}
    def tr(e):
        return tuple(Var(subst[t.name]) if isinstance(t,Var) else t for t in e)
    used={t.name for t in word_expression if isinstance(t,Var)}
    if not used <= set(subst):
        raise ValueError('Undeclared output variable')
    out=['(set-logic QF_SLIA)', '(set-option :produce-models true)',
         '(set-option :timeout %d)'%timeout_ms,
         '(set-option :smt.string_solver %s)'%engine]
    for name,reg in R.domains:
        out.append('(declare-const %s String)'%subst[name])
        out.append('(assert (str.in_re %s %s))'%(subst[name],regex_smt(reg)))
    for a,b in R.equations:
        out.append('(assert (= %s %s))'%(smt_expr(tr(a)),smt_expr(tr(b))))
    out += ['(declare-const out_word String)',
            '(assert (= out_word %s))'%smt_expr(tr(word_expression))]
    if mode=='bad':
        C=regex_smt(admissible_regex(I))
        # Literal complement is regular; no negative equality/length theory.
        not_candidate='(str.in_re out_word (re.comp %s))'%C
        cases=[]
        for p,q in sorted(I.flags):
            a=path_regex(I.delta,I.start,(p,))
            b=path_regex(I.delta,p,(q,))
            c=path_regex(I.delta,q,tuple(sorted(I.final)))
            if a is not None and b is not None and c is not None:
                cases.append('(and (str.in_re cut_x %s) (str.in_re cut_d %s) (str.in_re cut_z %s))'%(regex_smt(a),regex_smt(b),regex_smt(c)))
        for name in ('cut_x','cut_d','cut_z','cut_t'):
            out.append('(declare-const %s String)'%name)
            out.append('(assert (str.in_re %s %s))'%(name,regex_smt(BINARY)))
        paths='false' if not cases else cases[0] if len(cases)==1 else '(or '+' '.join(cases)+')'
        flag_case='(and (str.in_re out_word %s) (= out_word (str.++ cut_x cut_d cut_z)) (= (str.++ cut_d cut_z) (str.++ cut_z cut_t)) %s)'%(C,paths)
        out.append('(assert (or %s %s))'%(not_candidate,flag_case))
    out.append('(check-sat)')
    return '\n'.join(out)+'\n'


def _parse_values(text):
    # Models contain only binary strings, including empty. No numeric coercion.
    values={}
    for name,value in re.findall(r'\(([A-Za-z][A-Za-z0-9_]*)\s+"([01]*)"\)',text):
        values[name]=value
    return values


def run_script(script,names,wall_seconds=8):
    if wall_seconds<=0:
        raise ValueError('wall_seconds must be positive')
    runner=Path(__file__).with_name('_word_smt_native.py')
    try:
        p=subprocess.run([sys.executable,str(runner),','.join(names)],input=script,
                         capture_output=True,text=True,timeout=wall_seconds)
    except subprocess.TimeoutExpired:
        return {'status':'UNKNOWN','reason':'Wall-clock cap'}
    lines=p.stdout.strip().splitlines()
    status=lines[0] if lines else 'unknown'
    if p.returncode or status not in ('sat','unsat','unknown') or '(error' in p.stdout:
        return {'status':'UNKNOWN','reason':'Backend unavailable or error',
                'details':(p.stdout+p.stderr)[:300]}
    version=next((s[2:] for s in lines if s.startswith('; Z3 version ')),None)
    if status=='unknown':
        return {'status':'UNKNOWN','reason':'Incomplete backend or solver timeout','backend':version}
    return {'status':status.upper(),'values':_parse_values(p.stdout),'backend':version}


def check_family(I,R,word_expression,timeout_ms=5000,wall_seconds=8,engine='seq'):
    """Resource-bounded supplied-family check; positive/negative is family-scoped.

    COUNTEREXAMPLE is a directly checked bad member, not NO for the instance.
    VALID_FAMILY_SMT is universal inclusion backed by UNSAT, NOT an independent
    proof certificate. INHABITED plus such inclusion yields a verified witness.
    VACUOUS means the supplied family is empty. UNKNOWN stays inconclusive.
    """
    names=['v_'+n for n,_ in R.domains]+['out_word','cut_x','cut_d','cut_z','cut_t']
    bad=run_script(family_script(I,R,word_expression,'bad',timeout_ms,engine),names,wall_seconds)
    if bad['status']=='UNKNOWN':
        return bad
    if bad['status']=='SAT':
        vals=bad['values']; assignment={n:vals.get('v_'+n) for n,_ in R.domains}
        if any(x is None for x in assignment.values()):
            return {'status':'UNKNOWN','reason':'Incomplete concrete model'}
        w=evaluate(word_expression,assignment)
        if not R.satisfies(assignment) or vals.get('out_word')!=w or witness(I,w) or border_witness(I,w):
            return {'status':'UNKNOWN','reason':'Model failed independent validation'}
        detail={'status':'COUNTEREXAMPLE','word':w,'assignment':assignment,'backend':bad['backend']}
        if I.admissible(w):
            cuts=[vals.get('cut_'+n) for n in ('x','d','z','t')]
            if any(c is None for c in cuts):
                return {'status':'UNKNOWN','reason':'Missing cut model'}
            x,d,z,t=cuts
            if w!=x+d+z or d+z!=z+t:
                return {'status':'UNKNOWN','reason':'Invalid equation certificate'}
            c=I.run(w); pair=(c[len(x)],c[len(x)+len(d)])
            if pair not in I.flags:
                return {'status':'UNKNOWN','reason':'Invalid flag certificate'}
            detail.update(cuts={'x':x,'d':d,'z':z,'t':t},flag=list(pair))
        else:
            detail['reason']='Not an admissible accepted word'
        return detail
    base=run_script(family_script(I,R,word_expression,'base',timeout_ms,engine),
                    ['v_'+n for n,_ in R.domains]+['out_word'],wall_seconds)
    if base['status']=='UNSAT':
        return {'status':'VACUOUS_SMT','reason':'Supplied family empty under backend','backend':base['backend']}
    if base['status']=='UNKNOWN':
        return {'status':'UNKNOWN','reason':'No bad member, but inhabitance unresolved','backend':bad['backend']}
    vals=base['values']; assignment={n:vals.get('v_'+n) for n,_ in R.domains}
    if any(x is None for x in assignment.values()):
        return {'status':'UNKNOWN','reason':'Missing inhabitance model'}
    w=evaluate(word_expression,assignment)
    if not R.satisfies(assignment) or not witness(I,w) or not border_witness(I,w):
        return {'status':'UNKNOWN','reason':'Inhabitance model failed independent predicates'}
    return {'status':'VALID_FAMILY_SMT','word':w,'assignment':assignment,'backend':bad['backend'],
            'trust':'Universal inclusion uses backend UNSAT; witness is independently checked',
            'scope':'One supplied family; not a decision for unrestricted existence'}
