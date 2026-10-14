WILF FINITE COVER FOR 14..37

Python 3.9 or later; standard library only; exact integers.
See ../README.md for download, integrity-check and reproduction instructions.

Run a complete computation:
  python3 -E -s -B cover.py --output /chosen/path/run
Check an existing run:
  python3 -E -s -B verify.py /chosen/path/run
Replay and compare its mathematical event streams:
  python3 -E -s -B verify.py /chosen/path/run --rerun --output /chosen/path/replay

Use a fresh output directory. --n selects cases in 14..37. A resource ceiling
specified by --max-nodes can leave unresolved branches and does not prove
closure. Passing relaxed parameters do not assert semigroup realizability.

The four journal stages are profiles, allocations, tuples and labels.
RULES.json and proofs/ describe the mathematical domains, rules and imports.
The case 13 is not computed. The inclusive conductor bound c<=200 is admitted
from Bacher, not rerun; no larger conjecture-assisted range is imported.

The checker performs partial validation and same-implementation replay; it
is not an independent complete verifier or a formal proof kernel. Mathematical
soundness depends on the ordinary proofs, exact import hypotheses and the
paper-to-code correspondence discussed in the manuscript. Original rule
numbering is retained. The manuscript supplies the final mathematical account.

MANIFEST.json binds the case manifests and the checker source files. The
per-case manifests bind the four compressed journals and their decompressed
mathematical event streams.
