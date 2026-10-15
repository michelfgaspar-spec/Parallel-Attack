# Finite checks of the graceful labeling construction

Requires Python 3.9 or later with its standard library. Keep assertions enabled.

From this directory, run both commands:

```sh
python3 -E -s -B support/verify_extension.py
python3 -E -s -B support/check_construction.py
```

The first program constructs and checks the complete labeled tree for every pair `1 <= u, v <= 100`. It checks the vertex labels, edge differences, root label, and branch profiles of the current three-leaf-star family. The two exceptional small assignments remain in `support/small_solutions.json`. Success reports `checked_pairs: 10000`.

The second program compares 70 literal parent entries from Table 3 at q=27, Table 4 at q=25, and equations (9) and (16) at q=29, with the base construction. These t=0 boundary rows are in `support/formula_boundaries.json`. Entry positions are leaf labels 6,...,q-5; entry values are their parents. Repeated parent values are required for stars and are distinct from duplicated vertex labels.

Fourteen explicitly listed route and boundary cases check the base graph, first transfer, redistributed graph and split graph. Each stage has bijective vertex labels, exact differences, connectivity, diameter six and unique centre zero. Transfers preserve both anchor leaves; redistribution uses available reflection pairs in increasing order of smaller labels. The two exceptional witnesses are given directly before the split, so their first three checkpoints coincide. Rejection controls alter a formula parent, duplicate a vertex label, omit a split edge, use the unavailable generic q=27 first transfer, and change the selected redistribution order.

To inspect complete checkpoint data, add `--output /path/to/new/graceful-checkpoints.json` to the second command. `assignment(u, v, checkpoints=True)` also returns the three parent maps and final split edges. The checkpoint file is optional output, not an input. Success reports `status: pass` and `formula_parent_entries: 70`.

These finite checks complement the all-parameter theorem. The adjacent Lean project now supplies a computable labeling for every positive parameter pair, with proved root-zero gracefulness, numerical anchors and the prescribed ordering. The finite programs do not establish that universal result. All six numerical constructions before the split, including both exceptional tables, are now proved to correspond to the independently defined merged graph. The printed anchor, parent, transfer and cycle formulas also have exact formal counterparts. These Lean results establish the all-parameter construction; the Python programs provide separate finite checks and have not been formalized as Python executions in Lean.
