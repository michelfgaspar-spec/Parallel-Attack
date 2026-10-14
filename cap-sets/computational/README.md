# Finite parabola cap-set verification

Requires Python 3.9 or later and its standard library. From this directory, run both checks, using new receipt filenames outside this directory:

```sh
python3 -E -s -B verification/verify.py --output /tmp/h41-result.json
python3 -E -s -B verification/verify_two_cosets.py --output /tmp/two-cosets-result.json
```

The first program reconstructs the field and order-41 subgroup, recomputes the forbidden triples, checks the complete normalized extension family, and verifies the witness and classification. Expected results are maximum coefficient cardinality five, 328 maximizers, and 32,800 cap points.

The second program checks all same-coset and cross-coset pairs, the repeated-coefficient obstructions, and the specified two-coset domain. Its classification combines those checks with the first program's subgroup result and the manuscript's symbolic scaling argument. Both programs must pass; their receipts report `status: pass`.

The five JSON inputs are in `verification/data/`. These results concern only the coefficient domains specified in the manuscript.

The parabola construction and discriminant criterion follow Cassie Grace and Jose Felipe Voloch, *Algebraic Capsets*, [DOI 10.1002/jcd.70024](https://doi.org/10.1002/jcd.70024), and their [associated implementation](https://github.com/cassie-grace/capsets). The supplied checkers implement the restricted finite verification described in the accompanying manuscript and supplement.
