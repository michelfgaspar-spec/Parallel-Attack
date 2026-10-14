# Parallel Attack

Parallel Attack is a coordinated AI attack on selected mathematical problems. We investigate how techniques, representations, and results can be transferred from one topic to another, and what must be preserved for those transfers to remain valid.

This is part of an ongoing investigation into the mathematical performance of AI models and the underlying calculus of their reasoning: how they choose representations, reuse arguments, compress information, retain evidence, and work with formal proofs. The work combines mathematical exploration, literature analysis, computation, review, and Lean formalization.

## Reading the results

The seven problem folders contain manuscript PDFs, any included supplements, a separate Lean project in `lean/`, and finite computational companions in `computational/`.

- **Manuscripts** present the arguments and their relationship to existing mathematics for human evaluation.
- **Computer-assisted arguments** depend on specified algorithms, finite input or certificate data, and the coverage established by their checks. The companions below support the stated finite cases; complete executable packages are not yet available for every claim.
- **Lean formalizations** provide kernel-checked evidence for the encoded statements under their stated hypotheses. They contain completed proofs alongside definitions, specifications, and results whose required inputs remain open.

All seven Lean projects have passed separate builds with the recorded toolchain and dependency pins. Proof coverage and manuscript-to-code correspondence remain partial. The repository does not promise AI reproducibility of the arguments: another model run need not recover the same reasoning or discovery process.

## The problems

### ARRIVAL and rotor routing

ARRIVAL asks whether a deterministic walk through a graph of alternating switches reaches its destination. Its [2016 introduction](https://arxiv.org/abs/1605.03546) established membership in NP ∩ coNP. Rotor-routing and abelian-network methods provide ways to reason about long executions through their accumulated effects.

We study how much phase information a small interface must retain when it is connected to another component. The [manuscript](arrival/Rotor_Interface.pdf) develops a two-entry interface with a period-four passive reset, a cyclic description with `3k + 4` canonical states for line length `k`, and decoders for a single interface and two coupled copies. Least stabilization distinguishes physically meaningful feedback counts from arbitrary algebraic fixed points. The [Lean project](arrival/lean/) checks scalar decoder algebra and selected routing lemmas; full physical termination, decoding, and implementation-cost bridges remain open.

### Graceful trees

The graceful tree conjecture dates to the 1960s. It asks whether every tree with `q` edges can be labeled with `0, …, q` so that its edge differences are exactly `1, …, q`. [Transfer constructions](https://arxiv.org/abs/1402.6570v2) developed sufficient conditions for families of diameter-six trees by redistributing leaves while preserving graceful labels.

We ask whether a particular two-parameter family admits a graceful labeling with its centre labeled zero. The revised [manuscript](graceful-trees/Root_Zero_Graceful_Trees.pdf) extends an earlier family by introducing a three-leaf star and checking the necessary transfers for every positive parameter pair. The [Lean project](graceful-trees/lean/) proves root-zero labeling existence for the encoded family for all positive `u, v`. Correspondence with the manuscript's graph and diameter presentation, and extraction of an executable explicit labeling procedure, remain separate obligations.

### Lebesgue universal covering

Lebesgue's [1914 covering problem](https://arxiv.org/abs/1502.01251) asks for a convex planar set of least area that can contain a rigidly moved copy of every set of diameter one. Successive geometric constructions and numerical refinements have developed upper and lower bounds.

We study a test family consisting of a disk, a Reuleaux triangle, and a Reuleaux pentagon. Can low-area placements be confined to a bounded translation region, and can a bound at one angle be propagated to nearby angles? The [manuscript](universal-covering/Universal_Covering.pdf) derives explicit confinement estimates and angular continuity bounds for a clipped area infimum. Its application to inherited regional numerical premises leaves two positive angular gaps, so it gives no new global numerical lower bound. The [Lean project](universal-covering/lean/) proves selected analytic and topological components; its geometric imports and admission of the numerical certificates into Lean remain open.

### Cap sets

A cap set over F₃ contains no three distinct points whose sum is zero. The [2016 polynomial-method breakthrough](https://arxiv.org/abs/1605.09223) gave exponential upper bounds and changed the study of large cap sets. Our question concerns an exact classification inside a specified construction family.

For unions of punctured parabolas over F₆₅₆₁, which coefficient sets are valid and largest within an order-41 subgroup, or its union with a coset of opposite quadratic character? The [manuscript](cap-sets/H41_Parabola_Cap_Sets.pdf) reports a maximum of five coefficients in both domains: 328 attaining sets in the subgroup and 656 in the two-coset domain, each yielding a 32,800-point cap. These are restricted classifications. The [Lean project](cap-sets/lean/) checks algebraic reductions and conditional certificate arguments; concrete field realization, table interpretation, and acceptance of the finite certificates remain open.

### Unit-distance colouring

The Hadwiger–Nelson problem asks how many colours are needed to colour the plane when points a unit distance apart must differ. In [2018, de Grey](https://arxiv.org/abs/1804.02385) exhibited finite unit-distance graphs requiring at least five colours, demonstrating the power of finite obstructions.

We investigate how a colouring obstruction in a finite quotient can be realized by actual geometric constraints. The [manuscript](unit-distance-colouring/Cyclotomic_Unit_Distance.pdf) specifies a finite construction using cyclotomic coordinates, equality gadgets, shortest words, and shared forests, with an imported geometric forcing result. It reports that eighteen is the least number of retained whole lines giving an obstruction within its fixed twenty-one-line family, and reduces a word-length calculation to 147 candidates. The [Lean project](unit-distance-colouring/lean/) proves word-metric, gluing, and checker implications under stated inputs; the concrete geometry, seed applicability, and full certificate data still require admission.

### Parity games

Parity games model infinite behaviour in finite graphs and are used in automata theory and verification. The [2017 development of quasipolynomial algorithms and succinct progress measures](https://arxiv.org/abs/1702.05051) made compact strategy representations and ordered trees particularly useful tools.

We ask what strategy information must survive local changes, feedback, and the removal of a boundary vertex. The [manuscript](parity-games/Parity_Games.pdf) studies several restricted settings: joint outcomes under one policy, feedback counterexamples, normalization, path strategy iteration, and small universal trees. Its examples show that forward minimum profiles can lose feedback information and that minimal boundary summaries can lose information about non-returning plays. The [Lean project](parity-games/lean/) checks selected policy/history lemmas and an abstract one-feedback normalization rule. Physical compiler correspondence, complete boundary-table arguments, general algorithmic costs, and several tree representation bridges remain open.

### Wilf's inequality

For a numerical semigroup, let `c` be its conductor, `e` the number of minimal generators, and `n` the number of its elements below `c`, including zero. [Wilf's 1978 conjecture](https://arxiv.org/abs/1703.01761) asks whether `ne ≥ c`. Later developments connect this inequality with Apéry sets, algebraic growth bounds, and finite enumeration.

We investigate how structural bounds can reduce infinite families to finite domains, and how a certificate can establish that every required branch was covered. The [manuscript](wilf-13-37/Wilf_13-37.pdf) develops conductor reductions, Hilbert-function and matching bounds, and ordered enumeration and exhaustive-forest specifications. It reports an application to `13 ≤ n ≤ 37` using external and historical computational inputs. The [Lean project](wilf-13-37/lean/) proves structural, prefix, and checker lemmas, including twelve prefix properties. Full semigroup correspondence, concrete certificate acceptance, and complete computational coverage of the reported range remain open; the new enumeration specifications have not been executed as a full verification of that range.

## Transfer of techniques and evidence

Across these problems, we investigate exact encodings, symmetry reductions, local transformations, bounded searches, and certificates that preserve the connection between an abstract argument and its concrete objects. A useful compression must retain the information needed by the next operation: rotor phases, choices shared by a policy, geometric placements, or every branch of a finite search.

Evidence retention is part of that investigation. An argument needs recoverable premises, witnesses, source credit, and coverage information if it is to be reused, challenged, or revised. The findings above provide concrete cases for studying when a technique transfers successfully and when additional information or a new correspondence proof is required.

## Lean projects

Each problem's `lean/` directory contains its required local modules and pinned build configuration. With the specified toolchain and dependencies available, run `lake build` from that directory. Shared foundations are copied into the projects that use them, so a project's source imports do not require another problem folder.

## Computational companions

These are conventional mathematical checking programs and their finite data, with separate run instructions. Six companions use Python's standard library; universal covering additionally uses the pinned python-flint/Arb dependency for rigorous interval arithmetic. The manuscripts identify the relevant checks and their mathematical scope.

| Problem | Finite computation | Scope |
| --- | --- | --- |
| [ARRIVAL](arrival/computational/) | Decoder and routing comparisons in small instances | Supplementary finite checks |
| [Graceful trees](graceful-trees/computational/) | Complete labeling checks for 10,000 parameter pairs | Supplementary to the all-parameter proof |
| [Universal covering](universal-covering/computational/) | 43 core cases, 286 middle-strip cells, restricted certificates, endpoint pilot and angular propagation arithmetic | Stated regional and restricted domains, with the manuscript's analytic arguments; two angular gaps remain |
| [Cap sets](cap-sets/computational/) | Subgroup and two-coset certificate checks | Exact classification within the specified coefficient domains; run both verifiers |
| [Parity games](parity-games/computational/) | Forward-profile collision and feedback | Four selected graphs in the stated example |
| [Unit-distance colouring](unit-distance-colouring/computational/) | Words, fibres, local geometry, matching, coordinate bounds, and line selection | Finite construction checks; seed forcing remains a cited input |
| [Wilf](wilf-13-37/computational/) | Finite-cover generation and recorded-case checking for `14 ≤ n ≤ 37` | Partial recorded validation and same-implementation replay; the newer general algorithms are separate specifications |

The first six companions' manuscript references identify version [`companions-v1`](https://github.com/michelfgaspar-spec/Parallel-Attack/releases/tag/companions-v1). Universal covering's manuscript references identify [`companions-v2`](https://github.com/michelfgaspar-spec/Parallel-Attack/tree/companions-v2/universal-covering/computational). Wilf's large execution archive remains an asset of `companions-v1`; its README gives the checksum and commands. The repository and release assets are currently private and require repository access.
