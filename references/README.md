# References

One file per publication the formalization draws on, listing that paper's
results and, for each, where it is formalized — so "is Prop. 3.3 done?" is a
lookup rather than a search.

A file's `## References` block says which papers it draws on and `[1, Prop. 3.3]`
says which result; these pages are that relation read the other way. Keeping the
two in step is `scripts/check-references.py`'s job, which CI runs: it fails if a
cited paper has no page here, if a link points at a file that does not cite that
paper, if a result cited in the tree is missing from a table, if a row deferring
to an earlier paper names a row that is not on that paper's page, or if a count
below disagrees with the table it summarizes.

One directory per year of publication, so a paper is where its year says.

**The counts are of the paper, not of the tree.** A row exists for every result
in scope, formalized or not, so the denominator does not move when we do more
work — that is what makes the fraction mean something.

`🟡 9/22 | 5` reads *nine of the twenty-two results in scope are formalized, and
five more are out of scope*. 🟢 is everything in scope · 🟡 some of it · 🔴 none
yet · ⚪ the paper has not been read. A paper with nothing in scope at all is
green: there is nothing outstanding. Green is the goal, and the way to it is
formalizing what is in scope — never by moving an awkward row out of it.

**What may sit outside the count.** Only these, and each says which in its own
row, so the reason travels with the result:

* a result the paper **restates from an earlier one** — it belongs to that
  paper's page, and counting it twice would flatter both;
* a result **Mathlib already provides**, which we use rather than reprove;
* something that **is not a claim to formalize** — a remark, an experiment, a
  discussion of when to prefer one method to another;
* a result we have **decided to do differently on purpose**, which means there is
  a row in [FINDINGS.md](../FINDINGS.md) saying why;
* a result **about a subject CORALean does not cover** — several papers are cited
  for one thing and spend the rest elsewhere, and Grönwall's 1919 note is the
  clearest case: we use its inequality and have no use for the differentiability
  of a solution with respect to a parameter, which is what the paper is actually
  about. The row says which subject, so the claim can be argued with.

Anything else that is not yet formalized is `—`, and stays in the denominator.
"Hard" is not a reason to leave the denominator; "we do not do this at all" is.

| Paper | Authors | Venue | Year | Formalized |
|---|---|---|---|---|
| [Note on the derivatives with respect to a parameter of the solutions of a system of differential equations](1919/gronwall-annals-derivatives.md) | Gronwall | Annals of Mathematics, 20(4):292-296 | 1919 | 🟢 0/0 \| 6 |
| [An embedding theorem for spaces of convex sets](1952/radstrom-embedding.md) | Rådström | Proc. Amer. Math. Soc. 3, pp. 165-169 | 1952 | ⚪ 0/0 \| 0 |
| [A state bounding observer based on zonotopes](2003/combastel-ecc-state-bounding-observer.md) | Combastel | ECC | 2003 | 🟢 5/5 \| 1 |
| [Reachability Analysis and its Application to the Safety Assessment of Autonomous Cars](2010/althoff-thesis.md) | Althoff | PhD thesis, TU München | 2010 | 🟢 33/33 \| 3 |
| [Analyzing Reachability of Linear Dynamic Systems with Parametric Uncertainties](2011/althoff-reachability-parametric-uncertainties.md) | Althoff, Krogh, Stursberg | In A. Rauh and E. Auer (eds.), Modeling, Design, and Simulation of Systems with Uncertainties, Springer | 2011 | 🟡 2/4 \| 0 |
| [Reachability Analysis of Nonlinear Systems using Conservative Polynomialization and Non-Convex Sets](2013/althoff-hscc-conservative-polynomialization.md) | Althoff | HSCC | 2013 | 🟡 4/6 \| 2 |
| [On Computing the Minkowski Difference of Zonotopes](2015/althoff-arxiv-minkowski-difference.md) | Althoff | arXiv | 2015 | 🟡 4/15 \| 2 |
| [Semi-Supervised Classification with Graph Convolutional Networks](2017/kipf-iclr-gcn.md) | Kipf, Welling | ICLR | 2017 | 🟢 1/1 \| 4 |
| [Utilizing Dependencies to Obtain Subsets of Reachable Sets](2020/kochdumper-hscc-utilizing-dependencies.md) | Kochdumper, Schürmann, Althoff | HSCC | 2020 | 🟢 11/11 \| 4 |
| [Adaptive parameter tuning for reachability analysis of linear systems](2020/wetzlinger-cdc-adaptive-tuning.md) | Wetzlinger, Kochdumper, Althoff | CDC, pp. 5145–5152 | 2020 | 🟡 8/12 \| 1 |
| [Sparse Polynomial Zonotopes: A Novel Set Representation for Reachability Analysis](2021/kochdumper-tac-sparse-polyzonotopes.md) | Kochdumper, Althoff | IEEE Transactions on Automatic Control | 2021 | 🟢 21/21 \| 6 |
| [Adaptive Parameter Tuning for Reachability Analysis of Nonlinear Systems](2021/wetzlinger-hscc-adaptive-tuning-nonlinear.md) | Wetzlinger, Kulmburg, Althoff | HSCC | 2021 | 🟡 2/5 \| 1 |
| [Open- and Closed-Loop Neural Network Verification using Polynomial Zonotopes](2022/kochdumper-arxiv-nn-polyzono.md) | Kochdumper et al. | arXiv:2207.02715 | 2022 | 🟢 4/4 \| 3 |
| [Set operations and order reductions for constrained zonotopes](2022/raghuraman-koeln-constrained-zonotopes.md) | Raghuraman, Koeln | Automatica, 139:110204 | 2022 | 🟡 3/8 \| 9 |
| [Adaptive Reachability Algorithms for Nonlinear Systems Using Abstraction Error Analysis](2022/wetzlinger-nahs-abstraction-error.md) | Wetzlinger, Kulmburg, Le Penven, Althoff | Nonlinear Analysis: Hybrid Systems, 46:101252 | 2022 | 🟡 7/13 \| 2 |
| [Constrained Polynomial Zonotopes](2023/kochdumper-constrained-polyzonotopes.md) | Kochdumper, Althoff | Acta Informatica | 2023 | 🟢 17/17 \| 7 |
| [Automatic Abstraction Refinement in Neural Network Verification using Sensitivity Analysis](2023/ladner-hscc-abstraction-refinement.md) | Ladner, Althoff | HSCC | 2023 | 🟢 27/27 \| 9 |
| [Fully Automatic Neural Network Reduction for Formal Verification](2023/ladner-tmlr-network-reduction.md) | Ladner, Althoff | TMLR | 2023 | 🟢 8/8 \| 5 |
| [Backward Reachability Analysis of Perturbed Continuous-Time Linear Systems Using Set Propagation](2023/wetzlinger-arxiv-backward-reachability.md) | Wetzlinger, Althoff | arXiv:2310.19083 | 2023 | 🟡 1/11 \| 8 |
| [Fully-Automated Verification of Linear Systems Using Inner- and Outer-Approximations of Reachable Sets](2023/wetzlinger-fully-automated-verification.md) | Wetzlinger, Kochdumper, Bak, Althoff | IEEE Transactions on Automatic Control, vol. 68, no. 12, pp. 7771–7786 | 2023 | 🟡 1/19 \| 6 |
| [Fully-Automated Verification of Linear Systems Using Reachability Analysis with Support Functions](2023/wetzlinger-hscc-support-functions.md) | Wetzlinger, Kochdumper, Bak, Althoff | HSCC | 2023 | 🟢 5/5 \| 4 |
| [Exponent Relaxation of Polynomial Zonotopes and Its Applications in Formal Neural Network Verification](2024/ladner-aaai-exponent-relaxation.md) | Ladner, Althoff | AAAI | 2024 | 🟢 8/8 \| 6 |
| [Explaining Fast and Slow: Abstraction and Refinement of Provable Explanations](2025/bassan-icml-explaining-fast-and-slow.md) | Bassan, Elboher, Ladner, Althoff, Katz | ICML | 2025 | 🟢 14/14 \| 2 |
| [Formal Verification of Graph Convolutional Networks with Uncertain Node Features and Uncertain Graph Structure](2025/ladner-tmlr-gcn.md) | Ladner, Eichelbeck, Althoff | TMLR | 2025 | 🟢 12/12 \| 6 |

## Findings

Formalizing a paper turns things up. Where a printed result is wrong or a proof
does not follow, the paper's own page says so, under its own `## Findings`
heading — beside the result, where someone checking that result will be. These
pages carry one:

<!-- findings -->
* [Reachability Analysis and its Application to the Safety Assessment of Autonomous Cars](2010/althoff-thesis.md)
* [Reachability Analysis of Nonlinear Systems using Conservative Polynomialization and Non-Convex Sets](2013/althoff-hscc-conservative-polynomialization.md)
* [On Computing the Minkowski Difference of Zonotopes](2015/althoff-arxiv-minkowski-difference.md)
* [Utilizing Dependencies to Obtain Subsets of Reachable Sets](2020/kochdumper-hscc-utilizing-dependencies.md)
* [Sparse Polynomial Zonotopes: A Novel Set Representation for Reachability Analysis](2021/kochdumper-tac-sparse-polyzonotopes.md)
* [Adaptive parameter tuning for reachability analysis of linear systems](2020/wetzlinger-cdc-adaptive-tuning.md)
* [Adaptive Parameter Tuning for Reachability Analysis of Nonlinear Systems](2021/wetzlinger-hscc-adaptive-tuning-nonlinear.md)
* [Adaptive Reachability Algorithms for Nonlinear Systems Using Abstraction Error Analysis](2022/wetzlinger-nahs-abstraction-error.md)
* [Constrained Polynomial Zonotopes](2023/kochdumper-constrained-polyzonotopes.md)
* [Automatic Abstraction Refinement in Neural Network Verification using Sensitivity Analysis](2023/ladner-hscc-abstraction-refinement.md)
* [Fully-Automated Verification of Linear Systems Using Inner- and Outer-Approximations of Reachable Sets](2023/wetzlinger-fully-automated-verification.md)
* [Fully-Automated Verification of Linear Systems Using Reachability Analysis with Support Functions](2023/wetzlinger-hscc-support-functions.md)
* [Exponent Relaxation of Polynomial Zonotopes and Its Applications in Formal Neural Network Verification](2024/ladner-aaai-exponent-relaxation.md)
* [Explaining Fast and Slow: Abstraction and Refinement of Provable Explanations](2025/bassan-icml-explaining-fast-and-slow.md)
* [Formal Verification of Graph Convolutional Networks with Uncertain Node Features and Uncertain Graph Structure](2025/ladner-tmlr-gcn.md)

[FINDINGS.md](../FINDINGS.md) is the other half, and stays at the root: the
places this formalization parts from CORA on purpose, which belong to no paper.

## Citing

Cite as the papers are cited in the source — `[1]`, or `[1, Prop. 3.1]` — and see
[CONTRIBUTING.md](../CONTRIBUTING.md#references) for what belongs in a `##
References` block. [FINDINGS.md](../FINDINGS.md) records where a source turned
out to be wrong; the row for such a result says so and points there.
