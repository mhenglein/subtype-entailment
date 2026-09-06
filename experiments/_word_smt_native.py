"""Small SMT-LIB runner using the optional system Z3 shared library.

Run in a child process: a caller can enforce a wall-time limit safely.
No Python z3-solver package is required. Input is SMT-LIB on stdin.
"""
import ctypes
import ctypes.util
import sys


def main():
    path = ctypes.util.find_library('z3')
    if path is None:
        print('unknown\n; Z3 shared library is not installed')
        return 2
    lib = ctypes.CDLL(path)
    def bind(name, args, result):
        f = getattr(lib, name); f.argtypes = args; f.restype = result
        return f
    ptr, text = ctypes.c_void_p, ctypes.c_char_p
    cfg = bind('Z3_mk_config', [], ptr)()
    context = bind('Z3_mk_context', [ptr], ptr)(cfg)
    bind('Z3_del_config', [ptr], None)(cfg)
    evaluate = bind('Z3_eval_smtlib2_string', [ptr, text], text)
    version = bind('Z3_get_full_version', [], text)().decode()
    script = sys.stdin.read()
    try:
        answer = evaluate(context, script.encode())
        decoded = answer.decode() if answer else 'unknown'
        print(decoded)
        if decoded.strip() == 'sat' and len(sys.argv) > 1:
            names = sys.argv[1].split(',')
            query = '(get-value (' + ' '.join(names) + '))'
            values = evaluate(context, query.encode())
            print(values.decode() if values else '; no values')
        print('; Z3 version ' + version)
    finally:
        bind('Z3_del_context', [ptr], None)(context)
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
