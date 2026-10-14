# Finite Wilf computation

This companion supplies the exact finite cover for left cardinalities 14 through 37 described in the manuscript. The case 13 is treated mathematically. The reductions and cited inputs, including Bacher's inclusive conductor bound `c <= 200`, are supplied by the manuscript and the mathematical references in `verifier/proofs/`.

Requires Python 3.9 or later, using only its standard library and exact integers. Run the commands below from this directory and use fresh output directories.

## Small generation and replay

```sh
python3 -E -s -B verifier/cover.py --n 14 --output /tmp/wilf-n14
python3 -E -s -B verifier/verify.py /tmp/wilf-n14 --rerun --output /tmp/wilf-n14-replay
```

Expected results are `CARDINALITY 14 closed`, `status: closed`, and identical complete event streams. The six supplied unit tests run from `verifier/` with `python3 -E -s -B -m unittest -v test_cover`.

## Recorded finite cases

Download the 607 MiB archive **Wilf_execution_companions_v1.tar** from the [Parallel Attack companions-v1 release](https://github.com/michelfgaspar-spec/Parallel-Attack/releases/tag/companions-v1). Access requires repository permission while the repository is private. The archive contains 24 case manifests and 96 compressed mathematical journals. The algorithm sources are included directly in `verifier/`.

Save the archive in `release-assets/`. With GitHub CLI access to the private repository:

```sh
gh release download companions-v1 --repo michelfgaspar-spec/Parallel-Attack --pattern Wilf_execution_companions_v1.tar --dir release-assets
```

The archive has 636,661,760 bytes and SHA-256:

```text
26c3bce9ced2999b256ea12964ebd8bafb9b35077d58316e654d51f2e4f3997c
```

Check the archive and every decompressed journal, then validate all recorded cases directly from the tar file:

```sh
python3 -E -s -B scripts/check_integrity.py --archive release-assets/Wilf_execution_companions_v1.tar --full
python3 -E -s -B verifier/verify.py release-assets/Wilf_execution_companions_v1.tar --archive --output /tmp/wilf-recorded-check
```

No extraction is needed. The first command checks the archive inventory, source identities, compressed and decompressed digests, and event counts; this is an integrity check. The second recomputes profile, allocation and tuple arithmetic, matching maxima and recorded child-coverage obligations. It reports one `status: closed` row for each cardinality 14 through 37 and writes `VALIDATION.json` in the chosen output directory. `results/MANIFEST.json`, the per-case manifests and `JOURNAL_INDEX.json` specify the finite inputs; `results/SHA256SUMS` supplies the archive checksum in standard format.

## Recompute the mathematical event streams

To regenerate and compare both an elementary case and a case exercising all four journal stages:

```sh
python3 -E -s -B verifier/verify.py release-assets/Wilf_execution_companions_v1.tar --archive --n 14 33 --rerun --output /tmp/wilf-replay-14-33
```

Omit `--n 14 33` to replay all 24 cases, or run `cover.py` without `--n` to generate the complete cover from its definitions. Full generation took about 73 minutes in the retained computation; runtime depends on hardware and Python version. Full replay also validates the recorded data before generation and needs additional disk space comparable to the 607 MiB journal archive. Resource limits such as `--max-nodes` can leave unresolved branches; unresolved output does not establish closure.

The default checker provides partial mathematical validation. `--rerun` additionally reconstructs rank/label eligibility, propagation and complete matching graphs and compares every deterministic event stream, using the same implementation as the generator. Soundness remains relative to the ordinary mathematical proofs, imported hypotheses and manuscript-to-code correspondence. The manuscript's newer general PRIMARY and exhaustive-forest algorithms are separate specifications and are not executed by this companion.
