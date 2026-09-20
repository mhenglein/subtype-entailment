# Clean project-cache reproduction

Date: 2026-09-20. Session: `publication-sequence-20260920`.
Related: A010/A018, C081/C084/C085, C030, [#65](https://github.com/mhenglein/subtail/issues/65).
Operator: parent integrator. No separate reproduction agent was launched.

## Result and exact scope

**PASS:** a fresh clone at
`ce48c8e265ab3deef46d734280cda3432514fe8f` completed all 18 selected release
steps in 218.477 seconds of summed step time. Its tracked and untracked working
tree was clean before and after the run. `lean/.lake` was initially absent;
no project build cache was copied. The installed Python and Lean toolchains
were reused. This is a fresh project build, not a fresh operating-system or
toolchain-installation test.

Environment: Linux AArch64, Python 3.13.14, Lean 4.33.1
(`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`), Lake 5.0.0-src+819816b.
The pinned Lake manifest lists no third-party Lean packages. The worker was
separate from the existing research checkout; that older checkout was untouched.
No special cloud provider or private SSH alias is needed to reproduce this run.

The [machine-readable receipt](../results/clean-reproduction.json) contains
exact commands, limits, times, log hashes, 312 input/source hashes, safe
environment fields, and compact audit readbacks. Original receipt hashes are
preserved. Private checkout and Python executable prefixes are replaced by
portable placeholders in the checked-in copy.

## Reproduce

Install the pinned tools, place `python3`, `lean` and `lake` on PATH, and use
a fresh clone of the repository with access appropriate to its visibility:

```sh
git clone https://github.com/mhenglein/subtail.git subtail-reproduction
cd subtail-reproduction
git checkout ce48c8e265ab3deef46d734280cda3432514fe8f
python3 scripts/reproduce_release.py
```

Use a new clone for a new clean-build attempt. The runner refuses an existing
`.lake`, dirty source tree, or existing output directory; it deletes no caches.
Its logs and receipt go to ignored `tmp/release-reproduction/`. A failed step
stops the run. A step hitting its cap is recorded as `UNKNOWN` and fails the
release check; it is never converted into a negative mathematical answer.

The initial build names the optional normalization, prepared solver, finite,
certificate and C030 targets explicitly. The default library alone does not
build `ExpressionNormalizationAudit`, which the C081 audit imports.

## What passed

| Check | Actual evidence |
|---|---|
| Fresh combined build | 39.602 seconds; pinned default and selected optional targets |
| Default core | `scripts/check_lean.py`, 103.935 seconds; scope remains the script's documented core |
| Normalization and C081 | Explicit normalization kernel replay; 91 declaration/axiom readbacks |
| Cached summary endpoint | Kernel replay; 47 declarations, including 23 executable definitions; five actual CLI cases including a deliberate `UNKNOWN` |
| Finite-tree endpoint | Kernel replay; 13 declarations; 308 native growth comparisons and nine CLI boundary cases |
| Supplied graph certificates | Kernel replay; 24 declarations; 34 native accept/reject cases |
| C030 | Three module kernel replays; 72 declaration checks and seven executable constructor checks; independent replay on 12,956 instances and 200,196 words |
| Border experiments | Existing independent experiment suite passed |
| Paper example | Exactly `true`, `false`, `false`, `true` |
| Actual countermodel | Alternating-spine input returned `NOT_ENTAILED`; certificate verification returned `VERIFIED` |
| Python and documentation | 77 Python tests; research index; 21 mapped and four ordinary paper results |

The C030 independent replay checker does not itself run Lean. Those checks
appear as separate runner steps. Similarly, the paper source-map check is not
a kernel replay or a mathematical review.

## Preserved failed attempt

An earlier fresh clone at `b63a90443c3b71d086a340785e83751c441190fc`
passed its 67-job combined build and default core. Its ad hoc harness then
failed the C081 audit because the optional normalization audit had not been
built. Lean reported that the object file for
`Subtail.ExpressionNormalizationAudit` did not exist. The original receipt
remains `FAIL`; it is embedded with its hash in the current receipt.

This was a harness setup error, not a failed theorem or an absent source
module. The committed portable runner fixed the build target list and started
again in another fresh clone. It did not repair the first receipt or reuse
that clone's project cache.

## Revision transfer and limits

At parent revision `4954986`, every recorded Lean, solver, checker, experiment,
fixture and paper-example hash still matches the successful run. The only
changed file among the runner's 312 recorded inputs is `paper/build.py`, for
PDF pagination. Rendering and source-map checks are repeated separately; no
old proof run is relabelled as a run at a later revision.

This selected release run does not repeat every historical experiment or the
matched 38-case and 19-case performance corpora. Their earlier receipts remain
historical evidence. It supplies no new terminal/shared-generator coverage,
six-variable completion, quantitative bound, or constructor extension.

The verified Lean decisions and supplied-certificate checker retain their
documented semantics. Python JSON parsing, launch, extraction and graph
finiteness checks remain external boundaries. A passing certificate is not a
formal completeness proof for the producer.

The technical reproduction portion of #65 is complete for this checkpoint.
The issue stays open for the owner-deferred author/license metadata and final
immutable release checkpoint. No new licensed release or release tag is claimed.
