# Finite rotor-coupling checks

Requires Python 3 with its standard library. Keep assertions enabled.

From this directory, run:

```sh
python3 -E -s -B check_coupling.py
```

The program compares the compressed decoder with direct routing on 7,620 canonical cases for line lengths 3 through 6, checks 324 all-even uncompressed cases, and checks positive feedback and zero-chip examples. A successful run prints `PASS` for these checks and an example of an algebraic fixed point that physical zero-chip routing does not select.

These are finite checks of the examples and decoder formulas. The general mathematical argument is in the accompanying manuscript.
