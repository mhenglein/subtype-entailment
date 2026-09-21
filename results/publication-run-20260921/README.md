# Fresh publication reproduction, 21 September 2026

Checked source: `a22d1fb323026fb1c10411d4418ceb03dd2798c2`.
[Summary and exact commands](../publication-reproduction-20260921.json).
The run used a new Linux clone with no project build cache, reusing installed
Python 3.13.14 and Lean 4.33.1. All 27 strict run gates passed; the stress gate
records six diagnostic UNKNOWN cases at the memory threshold, not six answers.

This directory preserves all 92 files from the execution output and the
separate quantitative receipt, including logs, subordinate JSON and generated
audit inputs. It is evidence, not a source directory imported by the library.
Private checkout/toolchain/home prefixes are normalized. Execution hashes in
receipts refer to the raw files. [The file index](file-hashes.json) gives both
original and stored SHA-256 values so normalization is not confused with a
byte-identical copy. Source-content hashes are unchanged.

The root wrapper records the one later source-inventory difference:
`paper/README.md` received a prose-only correction about Section 11's computable
bound. Render inputs, PDF, proof code, scripts, tests and workflows stayed
byte-identical. The final index/paper checks are recorded in the integration
receipt; the full fresh run is attributed only to its actual checked revision.
