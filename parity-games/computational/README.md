# Finite feedback-profile example

Requires Python 3 with its standard library. Keep assertions enabled.

From this directory, run:

```sh
python3 -E -s -B checks/check_forward_profile_collision.py --output /tmp/parity-feedback.json
```

The program computes outcomes in four finite selected graphs: two forward graphs and their two feedback alterations. It checks equality of the forward profiles and a difference after feedback. Success exits with code zero, prints the profiles, and writes the optional JSON result to the path given by `--output`. Omit that option to print results only.

The reported 45 vertices are in one selected graph. The manuscript's complete original policy arena also contains unselected menus and arms. This companion checks the selected graphs for the feedback example; its finite scope does not include the other algorithms or boundary operations in the manuscript.
