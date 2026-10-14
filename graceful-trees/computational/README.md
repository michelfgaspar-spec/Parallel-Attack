# Finite checks of the graceful labeling construction

Requires Python 3 with its standard library. Keep assertions enabled.

From this directory, run:

```sh
python3 -E -s -B support/verify_extension.py
```

The program constructs and checks the complete labeled tree for every pair `1 ≤ u, v ≤ 100`. It checks the vertex labels, edge differences, root label, and branch profiles of the current three-leaf-star family. The two exceptional small assignments are in `support/small_solutions.json`.

Success exits with code zero and reports `checked_pairs: 10000`. This finite run complements the manuscript's all-parameter argument.
