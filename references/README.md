# References

One file per publication the formalization draws on, listing that paper's
results and, for each, where it is formalized — so "is Prop. 3.3 done?" is a
lookup rather than a search.

A file's `## References` block says which papers it draws on and `[1, Prop. 3.3]`
says which result; these pages are that relation read the other way. Keeping the
two in step is `scripts/check-references.py`'s job, which CI runs: it fails if a
cited paper has no page here, if a link points at a file that does not cite that
paper, if a result cited in the tree is missing from a table, or if a count below
disagrees with the table it summarizes.

**The counts are of the paper, not of the tree.** A row exists for every result
in scope, formalized or not, so the denominator does not move when we do more
work — that is what makes the fraction mean something. Results with no bearing on
CORALean are marked `n/a` in their table and left out of the count, as is a
result the paper restates from an earlier one: that belongs to the earlier
paper's page, and counting it twice would flatter both.

🟢 everything in scope · 🟡 some of it · 🔴 none yet · ⚪ not yet inventoried

| Paper | Authors | Venue | Year | Formalized |
|---|---|---|---|---|
| [Note on the derivatives with respect to a parameter of the solutions of a system of differential equations](1919-gronwall-annals-derivatives.md) | Gronwall | Annals of Mathematics, 20(4):292-296 | 1919 | 🔴 0/6 |
| [An embedding theorem for spaces of convex sets](1952-radstrom-embedding.md) | Rådström | Proc. Amer. Math. Soc. 3, pp. 165-169 | 1952 | ⚪ 0/0 |
| [A state bounding observer based on zonotopes](2003-combastel-ecc-state-bounding-observer.md) | Combastel | ECC | 2003 | 🟡 1/6 |
| [Reachability Analysis and its Application to the Safety Assessment of Autonomous Cars](2010-althoff-thesis.md) | Althoff | PhD thesis, TU München | 2010 | 🟡 16/33 |
| [Analyzing Reachability of Linear Dynamic Systems with Parametric Uncertainties](2011-althoff-reachability-parametric-uncertainties.md) | Althoff, Krogh, Stursberg | In A. Rauh and E. Auer (eds.), Modeling, Design, and Simulation of Systems with Uncertainties, Springer | 2011 | 🟡 1/4 |
| [Reachability Analysis of Nonlinear Systems using Conservative Polynomialization and Non-Convex Sets](2013-althoff-hscc-conservative-polynomialization.md) | Althoff | HSCC | 2013 | 🔴 0/6 |
| [On Computing the Minkowski Difference of Zonotopes](2015-althoff-arxiv-minkowski-difference.md) | Althoff | arXiv | 2015 | 🟡 2/16 |
| [Semi-Supervised Classification with Graph Convolutional Networks](2017-kipf-iclr-gcn.md) | Kipf, Welling | ICLR | 2017 | 🟡 1/5 |
| [Utilizing Dependencies to Obtain Subsets of Reachable Sets](2020-kochdumper-hscc-utilizing-dependencies.md) | Kochdumper, Schürmann, Althoff | HSCC | 2020 | 🔴 0/14 |
| [Adaptive parameter tuning for reachability analysis of linear systems](2020-wetzlinger-cdc-adaptive-tuning.md) | Wetzlinger, Kochdumper, Althoff | CDC, pp. 5145–5152 | 2020 | 🔴 0/13 |
| [Sparse Polynomial Zonotopes: A Novel Set Representation for Reachability Analysis](2021-kochdumper-tac-sparse-polyzonotopes.md) | Kochdumper, Althoff | IEEE Transactions on Automatic Control | 2021 | 🟡 9/22 |
| [Open- and Closed-Loop Neural Network Verification using Polynomial Zonotopes](2022-kochdumper-arxiv-nn-polyzono.md) | Kochdumper et al. | arXiv:2207.02715 | 2022 | 🔴 0/5 |
| [Set operations and order reductions for constrained zonotopes](2022-raghuraman-koeln-constrained-zonotopes.md) | Raghuraman, Koeln | Automatica, 139:110204 | 2022 | 🟡 1/17 |
| [Constrained Polynomial Zonotopes](2023-kochdumper-constrained-polyzonotopes.md) | Kochdumper, Althoff | Acta Informatica | 2023 | 🟡 9/19 |
| [Automatic Abstraction Refinement in Neural Network Verification using Sensitivity Analysis](2023-ladner-hscc-abstraction-refinement.md) | Ladner, Althoff | HSCC | 2023 | 🟡 6/36 |
| [Fully Automatic Neural Network Reduction for Formal Verification](2023-ladner-tmlr-network-reduction.md) | Ladner, Althoff | TMLR | 2023 | 🟡 4/9 |
| [Fully-Automated Verification of Linear Systems Using Inner- and Outer-Approximations of Reachable Sets](2023-wetzlinger-fully-automated-verification.md) | Wetzlinger, Kochdumper, Bak, Althoff | IEEE Transactions on Automatic Control, vol. 68, no. 12, pp. 7771–7786 | 2023 | 🔴 0/22 |
| [Exponent Relaxation of Polynomial Zonotopes and Its Applications in Formal Neural Network Verification](2024-ladner-aaai-exponent-relaxation.md) | Ladner, Althoff | AAAI | 2024 | 🟡 8/9 |
| [Explaining Fast and Slow: Abstraction and Refinement of Provable Explanations](2025-bassan-icml-explaining-fast-and-slow.md) | Bassan, Elboher, Ladner, Althoff, Katz | ICML | 2025 | 🟡 9/14 |
| [Formal Verification of Graph Convolutional Networks with Uncertain Node Features and Uncertain Graph Structure](2025-ladner-tmlr-gcn.md) | Ladner, Eichelbeck, Althoff | TMLR | 2025 | 🟡 10/14 |

Cite as the papers are cited in the source — `[1]`, or `[1, Prop. 3.1]` — and see
[CONTRIBUTING.md](../CONTRIBUTING.md#references) for what belongs in a `##
References` block. [FINDINGS.md](../FINDINGS.md) records where a source turned
out to be wrong; the row for such a result says so and points there.
