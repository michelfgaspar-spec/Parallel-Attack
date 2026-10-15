# Graceful Trees Lean companion

This project formalizes the all-positive-parameter construction in the adjacent
[manuscript](../Root_Zero_Graceful_Trees.pdf). For every positive integer pair
`u, v`, it gives a computable graceful labeling of the family with branch leaf
multiplicities `(1,1,3)`, `(1,1,2v)` and `(1,2u)`, with zero at the unique centre.
The family has `q = 19 + 2(u + v)` edges and diameter six.

## Build

Use **Lean 4.33.0** and its Lake executable. The supplied `lean-toolchain`,
`lakefile.toml` and `lake-manifest.json` pin the compiler and dependencies;
Mathlib is pinned to `db584cd6d46c92f209a44c0f1c829460d327499d`.

From this directory, with the toolchain installed, run:

```sh
lake exe cache get
lake build
```

The first command retrieves the dependency build cache and can require network
access. With dependencies available, `lake build` checks the default `Partials`
target, which includes all 19 local Lean source files. The `Partials` namespace
is local to this project; every required local source is included here.

## Manuscript-to-code guide

Names below are relative to `Partials.Graceful`.

| Manuscript result | Main declarations | Source |
| --- | --- | --- |
| Theorem 1, for every positive `u, v` | `main_root_zero`, `Executable.label`, `Executable.label_graceful` | [Assembly](Partials/Graceful/Assembly.lean), [Executable](Partials/Graceful/Executable.lean) |
| Diameter six, unique centre, and its zero label | `diameter_six`, `center_eq_root`, `main_center_zero` | [Geometry](Partials/Graceful/Geometry.lean), [CentreZero](Partials/Graceful/CentreZero.lean) |
| Pair transfer and star split | `Operations.pairTransfer_preservesGraceful`, `Operations.starSplit_preservesGraceful` | [Operations](Partials/Graceful/Operations.lean) |
| Four symbolic constructions and their realization | `NumericConstruction.standard0_constructed`, `NumericConstruction.standard1_constructed`, `NumericConstruction.standard2_constructed`, `NumericConstruction.alternate_constructed` | [Symbolic](Partials/Graceful/Symbolic.lean), [NumericConstruction](Partials/Graceful/NumericConstruction.lean), [Realization](Partials/Graceful/Realization.lean) |
| Two literal exceptional assignments | `small23_root_zero`, `small27_root_zero` | [Witnesses](Partials/Graceful/Witnesses.lean) |
| Original and reordered graph presentations | `ManuscriptPresentation.originalIso`, `ManuscriptPresentation.reorderedIso`, `Executable.namedLabel_graceful`, `Executable.orderedLabel_graceful` | [ManuscriptPresentation](Partials/Graceful/ManuscriptPresentation.lean), [ReorderedPresentation](Partials/Graceful/ReorderedPresentation.lean), [ExecutableTransport](Partials/Graceful/ExecutableTransport.lean) |
| Merged graph before the split, on all six routes | `Executable.mergedEdge_iff_numeric` | [PreSplitCorrespondence](Partials/Graceful/PreSplitCorrespondence.lean) |
| Printed anchors, parent assignments, first transfers and cycles | `ManuscriptFormulas.anchor0_printed` and the other `*_printed` declarations | [ManuscriptFormulas](Partials/Graceful/ManuscriptFormulas.lean) |
| Prescribed order of reflection pairs | `Executable.pairStartsInOrder_strict`, `Executable.selected0_inOrder`, `Executable.selected1_inOrder`, `Executable.selected2_inOrder` | [ExecutableAnchors](Partials/Graceful/ExecutableAnchors.lean) |

The construction covers four symbolic routes and the two exceptional pairs
`(u,v) = (1,1)` and `(1,3)`. The predicate `AllPositiveTarget` spells out the
universal theorem; `RootZeroGraceful` requires bijective vertex labels, root label
zero, and every difference `1, …, q` exactly once.

To inspect the main declarations in Lean, use:

```lean
import Partials

#check Partials.Graceful.main_center_zero
#check Partials.Graceful.Executable.label_graceful
#print axioms Partials.Graceful.main_root_zero
```

The local declaration audit reports only the standard axioms `propext`,
`Classical.choice` and `Quot.sound` where used. The two finite exceptional
assignments also have Lean proofs. The universal construction is independent
of the bounded Python checks.

## Computational companion

The separate [computational companion](../computational/) supplies ordinary
standard-library Python programs and finite data, with its own run instructions.
It checks the documented 10,000 parameter pairs, 70 literal formula entries and
14 staged boundary constructions. These runs provide supplementary finite
evidence alongside the universal Lean proof and the manuscript's human-readable
argument.
