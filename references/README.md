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
| [An embedding theorem for spaces of convex sets](1952/radstrom-embedding.md) | Rådström | Proc. Amer. Math. Soc. 3, pp. 165-169 | 1952 | 🟢 3/3 \| 2 |
| [A state bounding observer based on zonotopes](2003/combastel-ecc-state-bounding-observer.md) | Combastel | ECC | 2003 | 🟢 5/5 \| 1 |
| [Taylor Models and Other Validated Functional Inclusion Methods](2003/makino-ijpam-taylor-models.md) | Makino, Berz | International Journal of Pure and Applied Mathematics, 4(4):379-452 | 2003 | 🟢 20/20 \| 24 |
| [Reachability of Uncertain Linear Systems Using Zonotopes](2005/girard-hscc-reachability-zonotopes.md) | Girard | HSCC, LNCS 3414, pp. 291-305 | 2005 | 🟢 7/7 \| 1 |
| [Verified Global Optimization with Taylor Model-based Range Bounders](2005/makino-tc-global-optimization.md) | Makino, Berz | Transactions on Computers, 11(4):1611-1618 | 2005 | 🟡 3/4 \| 6 |
| [Ellipsoidal Toolbox (ET)](2006/kurzhanskiy-cdc-ellipsoidal-toolbox.md) | Kurzhanskiy, Varaiya | CDC, pp. 1498-1503 | 2006 | 🟢 6/6 \| 14 |
| [Reachability Analysis of Nonlinear Systems with Uncertain Parameters using Conservative Linearization](2008/althoff-cdc-conservative-linearization.md) | Althoff, Stursberg, Buss | CDC, pp. 4042-4048 | 2008 | 🟡 10/11 \| 4 |
| [Zonotope/Hyperplane Intersection for Hybrid Systems Reachability Analysis](2008/girard-hscc-zonotope-hyperplane.md) | Girard, Le Guernic | HSCC, LNCS 4981, pp. 215-228 | 2008 | 🟡 5/7 \| 13 |
| [Safety Assessment for Stochastic Linear Systems using Enclosing Hulls of Probability Density Functions](2009/althoff-ecc-enclosing-hulls.md) | Althoff, Stursberg, Buss | ECC, pp. 625-630 | 2009 | 🟡 9/15 \| 5 |
| [Interval predictor models: Identification and reliability](2009/campi-automatica-interval-predictor-models.md) | Campi, Calafiore, Garatti | Automatica, 45(2):382-392 | 2009 | 🟡 4/9 \| 27 |
| [On the Hyperbox – Hyperplane Intersection Problem](2009/lara-infocomp-hyperbox-hyperplane.md) | Lara, Flores, Calderon | INFOCOMP Journal of Computer Science, 8(4):21-27 | 2009 | 🟢 18/18 \| 17 |
| [Computing Reachable Sets of Hybrid Systems Using a Combination of Zonotopes and Polytopes](2010/althoff-nahs-zonotopes-polytopes.md) | Althoff, Stursberg, Buss | Nonlinear Analysis: Hybrid Systems, 4(2):233-249 | 2010 | 🟢 13/13 \| 8 |
| [Reachability Analysis and its Application to the Safety Assessment of Autonomous Cars](2010/althoff-thesis.md) | Althoff | PhD thesis, TU München | 2010 | 🟡 33/34 \| 2 |
| [A Box-Consistency Contractor Based on Extremal Functions](2010/trombettoni-cp-box-consistency.md) | Trombettoni, Papegay, Chabert, Pourtallier | CP 2010, LNCS 6308, pp. 491-498 | 2010 | 🟢 9/9 \| 10 |
| [Zonotope Bundles for the Efficient Computation of Reachable Sets](2011/althoff-cdc-zonotope-bundles.md) | Althoff, Krogh | CDC-ECC, pp. 6814-6821 | 2011 | 🟢 16/16 \| 7 |
| [Analyzing Reachability of Linear Dynamic Systems with Parametric Uncertainties](2011/althoff-reachability-parametric-uncertainties.md) | Althoff, Krogh, Stursberg | In A. Rauh and E. Auer (eds.), Modeling, Design, and Simulation of Systems with Uncertainties, Springer | 2011 | 🟢 4/4 \| 0 |
| [Reachability Computation of Low-Order Models for the Safety Verification of High-Order Road Vehicle Models](2012/althoff-acc-low-order-models.md) | Althoff, Dolan | ACC, pp. 3559-3566 | 2012 | 🟢 3/3 \| 11 |
| [Avoiding Geometric Intersection Operations in Reachability Analysis of Hybrid Systems](2012/althoff-hscc-avoiding-intersection.md) | Althoff, Krogh | HSCC, pp. 45-54 | 2012 | 🟡 14/18 \| 4 |
| [Goffin's algorithm for zonotopes](2012/cerny-kybernetika-goffin-zonotopes.md) | Černý | Kybernetika, 48(5):890-906 | 2012 | 🟡 20/28 \| 18 |
| [Reachability Analysis of Nonlinear Systems using Conservative Polynomialization and Non-Convex Sets](2013/althoff-hscc-conservative-polynomialization.md) | Althoff | HSCC | 2013 | 🟢 6/6 \| 4 |
| [Zonotopic guaranteed state estimation for uncertain systems](2013/le-automatica-zonotopic-estimation.md) | Le, Stoica, Alamo, Camacho, Dumur | Automatica, 49(11):3418-3424 | 2013 | 🟡 13/14 \| 7 |
| [General Inner Approximation of Vector-valued Functions](2013/mullier-rc-general-inner-approximation.md) | Mullier, Goubault, Kieffer, Putot | Reliable Computing, 18:117-143 | 2013 | 🟡 14/15 \| 15 |
| [Reachability Analysis of Nonlinear Differential-Algebraic Systems](2014/althoff-tac-nonlinear-dae.md) | Althoff, Krogh | IEEE Transactions on Automatic Control, 59(2):371-383 | 2014 | 🟡 17/18 \| 17 |
| [Model Predictive Control with Signal Temporal Logic Specifications](2014/raman-cdc-mpc-stl.md) | Raman, Donzé, Maasoumy, Murray, Sangiovanni-Vincentelli, Seshia | CDC, pp. 81-87 | 2014 | 🟢 16/16 \| 17 |
| [On Computing the Minkowski Difference of Zonotopes](2015/althoff-arxiv-minkowski-difference.md) | Althoff | arXiv | 2015 | 🟢 16/16 \| 1 |
| [Discovering governing equations from data by sparse identification of nonlinear dynamical systems](2016/brunton-pnas-sindy.md) | Brunton, Proctor, Kutz | Proceedings of the National Academy of Sciences, 113(15):3932-3937 | 2016 | 🟢 9/9 \| 12 |
| [Dynamic mode decomposition with control](2016/proctor-siads-dmd-control.md) | Proctor, Brunton, Kutz | SIAM Journal on Applied Dynamical Systems, 15(1):142-161 | 2016 | 🟢 24/24 \| 17 |
| [STL Model Checking of Continuous and Hybrid Systems](2016/roehm-atva-stl-model-checking.md) | Roehm, Oehlerking, Heinz, Althoff | ATVA, LNCS 9938, pp. 412-427 | 2016 | 🟡 18/19 \| 3 |
| [Constrained zonotopes: A new tool for set-based estimation and fault detection](2016/scott-automatica-constrained-zonotopes.md) | Scott, Raimondo, Marseglia, Braatz | Automatica, 69:126-136 | 2016 | 🟡 10/13 \| 8 |
| [Implementation of Interval Arithmetic in CORA 2016](2017/althoff-arch-interval-arithmetic.md) | Althoff, Grebenyuk | ARCH16, EPiC Series in Computing 43, pp. 91-105 | 2017 | 🟢 19/19 \| 6 |
| [Time-Triggered Conversion of Guards for Reachability Analysis of Hybrid Automata](2017/bak-formats-time-triggered-conversion.md) | Bak, Bogomolov, Althoff | FORMATS, LNCS 10419, pp. 133-150 | 2017 | 🔴 0/4 \| 18 |
| [Forward Inner-Approximated Reachability of Non-Linear Continuous Systems](2017/goubault-hscc-forward-inner-reachability.md) | Goubault, Putot | HSCC, pp. 1-10 | 2017 | 🟡 3/4 \| 17 |
| [Semi-Supervised Classification with Graph Convolutional Networks](2017/kipf-iclr-gcn.md) | Kipf, Welling | ICLR | 2017 | 🟢 1/1 \| 4 |
| [Methods for Order Reduction of Zonotopes](2017/kopetzki-cdc-order-reduction.md) | Kopetzki, Schürmann, Althoff | CDC, pp. 5626-5633 | 2017 | 🟢 4/4 \| 4 |
| [Zonotopic Fault Detection Observer with H− Performance](2017/wang-ccc-fault-detection-observer.md) | Wang, Zhou, Puig, Cembrano, Wang | CCC, pp. 7230-7235 | 2017 | 🟡 11/15 \| 20 |
| [Implementation of Taylor Models in CORA 2018](2018/althoff-arch-taylor-models.md) | Althoff, Grebenyuk, Kochdumper | ARCH18, EPiC Series in Computing 54, pp. 145-173 | 2018 | 🟢 11/11 \| 38 |
| [AI2: Safety and Robustness Certification of Neural Networks with Abstract Interpretation](2018/gehr-sp-ai2.md) | Gehr, Mirman, Drachsler-Cohen, Tsankov, Chaudhuri, Vechev | IEEE S&P, pp. 3-18 | 2018 | 🟢 11/11 \| 4 |
| [On the parameterized computation of minimum volume outer ellipsoid of Minkowski sum of ellipsoids](2018/halder-cdc-minkowski-sum-ellipsoids.md) | Halder | CDC, pp. 4040-4045 | 2018 | 🟡 28/30 \| 13 |
| [Fast and Effective Robustness Certification](2018/singh-neurips-deepz.md) | Singh, Gehr, Mirman, Püschel, Vechev | NeurIPS | 2018 | 🟢 8/8 \| 6 |
| [Set-membership approach and Kalman observer based on zonotopes for discrete-time descriptor systems](2018/wang-automatica-descriptor-observer.md) | Wang, Puig, Cembrano | Automatica, 93:435-443 | 2018 | 🟡 16/18 \| 9 |
| [A distributed set-membership approach based on zonotopes for interconnected systems](2018/wang-cdc-distributed-set-membership.md) | Wang, Alamo, Puig, Cembrano | IEEE CDC, pp. 668-673 | 2018 | 🟢 4/4 \| 12 |
| [Linear Encodings for Polytope Containment Problems](2019/sadraddini-cdc-polytope-containment.md) | Sadraddini, Tedrake | CDC, pp. 4367-4372 | 2019 | 🟡 22/23 \| 16 |
| [Interval estimation methods for discrete-time linear time-invariant systems](2019/tang-tac-interval-estimation.md) | Tang, Wang, Wang, Raïssi, Shen | IEEE Transactions on Automatic Control, 64(11):4717-4724 | 2019 | 🟢 18/18 \| 22 |
| [Zonotopic set-membership state estimation for discrete-time descriptor LPV systems](2019/wang-tac-descriptor-lpv-estimation.md) | Wang, Wang, Puig, Cembrano | IEEE Transactions on Automatic Control, 64(5):2092-2099 | 2019 | 🟢 11/11 \| 16 |
| [Reachability Analysis of Large Linear Systems with Uncertain Inputs in the Krylov Subspace](2020/althoff-tac-krylov.md) | Althoff | IEEE Transactions on Automatic Control, 65(2):477-492 | 2020 | 🟡 7/13 \| 16 |
| [Scalable Zonotope-Ellipsoid Conversions using the Euclidean Zonotope Norm](2020/gassmann-acc-zonotope-ellipsoid.md) | Gaßmann, Althoff | ACC, pp. 4715-4721 | 2020 | 🟡 13/16 \| 14 |
| [Robust Under-Approximations and Application to Reachability of Non-Linear Control Systems With Disturbances](2020/goubault-lcss-robust-underapproximations.md) | Goubault, Putot | IEEE Control Systems Letters, 4(4):928-933 | 2020 | 🟡 5/7 \| 5 |
| [Reachability Analysis for Hybrid Systems with Nonlinear Guard Sets](2020/kochdumper-hscc-nonlinear-guards.md) | Kochdumper, Althoff | HSCC | 2020 | 🟡 13/16 \| 6 |
| [Utilizing Dependencies to Obtain Subsets of Reachable Sets](2020/kochdumper-hscc-utilizing-dependencies.md) | Kochdumper, Schürmann, Althoff | HSCC | 2020 | 🟢 11/11 \| 4 |
| [Adaptive parameter tuning for reachability analysis of linear systems](2020/wetzlinger-cdc-adaptive-tuning.md) | Wetzlinger, Kochdumper, Althoff | CDC, pp. 5145–5152 | 2020 | 🟢 12/12 \| 1 |
| [Guaranteed State Estimation in CORA 2021](2021/althoff-arch-state-estimation.md) | Althoff | ARCH21, EPiC Series in Computing 80, pp. 161-175 | 2021 | 🟢 4/4 \| 17 |
| [Sparse Polynomial Zonotopes: A Novel Set Representation for Reachability Analysis](2021/kochdumper-tac-sparse-polyzonotopes.md) | Kochdumper, Althoff | IEEE Transactions on Automatic Control | 2021 | 🟢 19/19 \| 10 |
| [On the co-NP-Completeness of the Zonotope Containment Problem](2021/kulmburg-ejc-zonotope-containment.md) | Kulmburg, Althoff | European Journal of Control, 62:84-91 | 2021 | 🟡 21/24 \| 4 |
| [Adaptive Parameter Tuning for Reachability Analysis of Nonlinear Systems](2021/wetzlinger-hscc-adaptive-tuning-nonlinear.md) | Wetzlinger, Kulmburg, Althoff | HSCC | 2021 | 🟢 5/5 \| 1 |
| [Benchmarks for the Formal Verification of Power Systems](2022/althoff-arch-power-systems.md) | Althoff | ARCH22, EPiC Series in Computing, vol. 90, pp. 26-43 | 2022 | 🟢 3/3 \| 18 |
| [Open- and Closed-Loop Neural Network Verification using Polynomial Zonotopes](2022/kochdumper-arxiv-nn-polyzono.md) | Kochdumper, Schilling, Althoff, Bak | arXiv:2207.02715; NFM 2023, LNCS, pp. 16-36 | 2022 | 🟡 3/4 \| 3 |
| [Set operations and order reductions for constrained zonotopes](2022/raghuraman-koeln-constrained-zonotopes.md) | Raghuraman, Koeln | Automatica, 139:110204 | 2022 | 🟡 9/11 \| 9 |
| [Adaptive Reachability Algorithms for Nonlinear Systems Using Abstraction Error Analysis](2022/wetzlinger-nahs-abstraction-error.md) | Wetzlinger, Kulmburg, Le Penven, Althoff | Nonlinear Analysis: Hybrid Systems, 46:101252 | 2022 | 🟡 13/14 \| 2 |
| [Scalable Zonotopic Under-approximation of Backward Reachable Sets for Uncertain Linear Systems](2022/yang-lcss-zonotopic-underapproximation.md) | Yang, Ozay | IEEE Control Systems Letters, 6:1555-1560 | 2022 | 🟢 15/15 \| 12 |
| [Distributed Set-Based Observers Using Diffusion Strategies](2023/alanwar-jfi-diffusion-observers.md) | Alanwar, Rath, Said, Johansson, Althoff | Journal of the Franklin Institute, 360(10):6976-6993 | 2023 | 🟡 6/8 \| 13 |
| [Checking and Establishing Reachset Conformance in CORA 2023](2023/althoff-arch-reachset-conformance.md) | Althoff | ARCH23, EPiC Series in Computing 96, pp. 9-33 | 2023 | 🟢 12/12 \| 13 |
| [Constrained Polynomial Zonotopes](2023/kochdumper-constrained-polyzonotopes.md) | Kochdumper, Althoff | Acta Informatica | 2023 | 🟢 16/16 \| 11 |
| [Automatic Abstraction Refinement in Neural Network Verification using Sensitivity Analysis](2023/ladner-hscc-abstraction-refinement.md) | Ladner, Althoff | HSCC | 2023 | 🟢 27/27 \| 10 |
| [Fully Automatic Neural Network Reduction for Formal Verification](2023/ladner-tmlr-network-reduction.md) | Ladner, Althoff | TMLR | 2023 | 🟢 14/14 \| 5 |
| [Guarantees for Real Robotic Systems: Unifying Formal Controller Synthesis and Reachset-Conformant Identification](2023/liu-tro-guarantees-real-robotic.md) | Liu, Schürmann, Althoff | IEEE Transactions on Robotics, 39(5):3776-3790 | 2023 | 🟢 15/15 \| 17 |
| [Reachability Analysis of ARMAX Models](2023/luetzow-cdc-armax.md) | Lützow, Althoff | CDC, pp. 7027-7034 | 2023 | 🟢 14/14 \| 5 |
| [Backward Reachability Analysis of Perturbed Continuous-Time Linear Systems Using Set Propagation](2023/wetzlinger-arxiv-backward-reachability.md) | Wetzlinger, Althoff | arXiv:2310.19083 | 2023 | 🟢 11/11 \| 9 |
| [Fully-Automated Verification of Linear Systems Using Inner- and Outer-Approximations of Reachable Sets](2023/wetzlinger-fully-automated-verification.md) | Wetzlinger, Kochdumper, Bak, Althoff | IEEE Transactions on Automatic Control, vol. 68, no. 12, pp. 7771–7786 | 2023 | 🟢 19/19 \| 6 |
| [Fully-Automated Verification of Linear Systems Using Reachability Analysis with Support Functions](2023/wetzlinger-hscc-support-functions.md) | Wetzlinger, Kochdumper, Bak, Althoff | HSCC | 2023 | 🟡 3/5 \| 4 |
| [Search-based and Stochastic Solutions to the Zonotope and Ellipsotope Containment Problems](2024/kulmburg-ecc-zonotope-ellipsotope-containment.md) | Kulmburg, Brkan, Althoff | ECC | 2024 | 🟡 13/18 \| 9 |
| [Exponent Relaxation of Polynomial Zonotopes and Its Applications in Formal Neural Network Verification](2024/ladner-aaai-exponent-relaxation.md) | Ladner, Althoff | AAAI | 2024 | 🟡 6/8 \| 6 |
| [Implementation of Polyhedral Operations in CORA 2024](2024/wetzlinger-arch-polyhedral-operations.md) | Wetzlinger, Kotsev, Kulmburg, Althoff | ARCH24, EPiC Series in Computing 103, pp. 163-181 | 2024 | 🟡 48/50 \| 15 |
| [Inner Approximations of Reachable Sets for Nonlinear Systems using the Minkowski Difference](2024/wetzlinger-lcss-inner-minkowski-difference.md) | Wetzlinger, Kulmburg, Althoff | IEEE Control Systems Letters, 8:2033-2038 | 2024 | 🟡 3/7 \| 16 |
| [Explaining Fast and Slow: Abstraction and Refinement of Provable Explanations](2025/bassan-icml-explaining-fast-and-slow.md) | Bassan, Elboher, Ladner, Althoff, Katz | ICML | 2025 | 🟢 14/14 \| 2 |
| [Robust Identification of Hybrid Automata from Noisy Data](2025/kochdumper-hscc-hybrid-automata-identification.md) | Kochdumper, Foughali, Habermehl, Asarin | HSCC, pp. 1-11 | 2025 | 🟢 9/9 \| 17 |
| [Set-Based Training for Neural Network Verification](2025/koller-tmlr-set-based-training.md) | Koller, Ladner, Althoff | TMLR | 2025 | 🟡 13/18 \| 24 |
| [Approximability of the Containment Problem for Zonotopes and Ellipsotopes](2025/kulmburg-tac-approximability-containment.md) | Kulmburg, Schäfer, Althoff | IEEE Transactions on Automatic Control | 2025 | 🟡 7/18 \| 31 |
| [Formal Verification of Graph Convolutional Networks with Uncertain Node Features and Uncertain Graph Structure](2025/ladner-tmlr-gcn.md) | Ladner, Eichelbeck, Althoff | TMLR | 2025 | 🟡 10/12 \| 7 |
| [Zono-Conformal Prediction: Zonotope-Based Uncertainty Quantification for Regression and Classification Tasks](2025/luetzow-jmlr-zono-conformal-prediction.md) | Lützow, Eichelbeck, Kochenderfer, Althoff | Journal of Machine Learning Research, 26(294):1-37 | 2025 | 🟢 13/13 \| 19 |
| [Reachset-Conformant System Identification](2026/luetzow-tac-reachset-conformant-identification.md) | Lützow, Althoff | IEEE Transactions on Automatic Control, 71(5):3014-3029 | 2026 | 🟡 13/14 \| 11 |

## CORA coverage

The tables above are by paper. [coverage/](coverage/README.md) is by CORA method: one table
per CORA class (`contSet`, `contDynamics`, `hybridDynamics`, `nn`), one row per method file
(`~/CORA/contSet/@zonotope/plus.m`), saying whether CORALean answers it:

* `proved`: a real-layer definition with an exact, outer or inner theorem;
* `float`: additionally a float-layer computable definition with an outer (or inner) theorem;
* `—`: not yet;
* `out-of-scope`, with one of six reasons: `plotting/display`, `random/sampling`,
  `solver-dependent`, `io/conversion-to-matlab-objects`, `matlab-runtime`, `deprecated`.
  "Hard" is never a reason.

A `proved` row without a float refinement is the float backlog. A row may carry a
`cora-issue` note where [FINDINGS.md](../FINDINGS.md) records that CORA's own implementation
is wrong. `scripts/check-references.py` checks the tables: every method file has a row,
every link resolves to a declaration the file has, a `proved` row links a theorem, a `float`
row a float-layer theorem, and the counts are the tables' counts.

## Theorem categories

`scripts/formalization-stats.py` also sorts every public theorem under `src/CORALean` into one
of four categories, mechanically: **paper theorems** (anything in a real-layer file some row of
these tables links), **float refinements** (a `Float/` path, or `Float` in the declaration or
file name; takes precedence, even when a row links the file), **proof helpers** (`aux_*`) and
**lemmas** (the rest). `Examples/` theorems are counted apart. The numbers are in
`experiments/paper/formalization-stats.json` and drawn in the paper's overview figure; see
`experiments/paper/latex/README.md`.

## The `Class` column

Every row ends in a `Class` cell, which is what the paper's figure on how much of
CORA is formalized and where the papers were wrong is made from
(`python3 scripts/formalization-stats.py`). The figure and the appendix break the classes
down by CORA class, by the first Lean file a row links; the mapping is in
[coverage/README.md](coverage/README.md#which-class-a-paper-result-lands-on).

A result in scope and formalized says how the **paper's** statement fared:
`correct` (as printed), `underspecified` (not false in the paper's setting, but a hypothesis, definition
or index is missing or misprinted, or a degenerate input is not excluded, and the
formalization supplies it),
`proof-gap` (the statement holds as printed, the printed proof does not establish
it), `fixed` (false on a non-degenerate input as printed, true after the correction the
row names, with a Lean counterexample linked), `false` (false and not repairable). Anything but `correct` gives its
reason in the cell after a dash, and the page's `## Findings` has the argument. A
row takes the most severe class that applies, and when unsure takes the milder
one: a claim that a paper is false has to be one the page can back.

**`fixed` and `underspecified` differ by the input the printed statement fails on.**
`fixed` is reserved for a statement that is false on a **non-degenerate input** — one
the paper's setting admits — and whose corrected form the formalization proves. A
degenerate edge case the paper's setting excludes is `underspecified`, with the
hypothesis the formalization supplies named in the note: the empty set (or an empty
operand), dimension zero, zero generators, an all-zero exponent column, a zero norm or a
zero run, and the like. `underspecified` otherwise keeps its meaning: not false in the
paper's setting, but a hypothesis, definition or index is missing and the formalization
supplies it. A statement that is false on a non-degenerate input because a hypothesis is
missing (a function that need not be continuous, a horizon shorter than the formula's
bound) is `fixed`, not `underspecified`. Properties of the input class that the
statement leaves open, such as the class of input signals, are `underspecified`.

**A `fixed` row links its counterexample.** The row's third cell names, after
`**Counterexample:**`, a Lean theorem declared in a file the row links, which exhibits a
non-degenerate input on which the printed statement fails (the file is named for the
theorem, `FooCounterexample.lean`/`foo_counterexample` where it can be, or `not_*`/`*_ne_*`
for a negation of the printed statement). `scripts/check-references.py` fails a `fixed`
row without the marker, and one whose named theorem is not declared in a linked file. A
row for which no counterexample is written says `**No counterexample:** <why>` with a
reason of at least 40 characters; these stay rare, and each is a debt.

Algorithm listings (every `Alg. n` row, and `Heuristic` rows) are read as intentionally
simplified pseudocode: a correction there counts as `underspecified`, never `fixed` or
`proof-gap`.

**`correct` means as printed.** The Lean theorem a `correct` row links states the paper's
result, not a neighbour of it. Where the formalization went another way, the row is settled
one of three ways: the printed statement is proved as well and linked (a stronger theorem
gets its one-line corollary in the printed form); or the row moves out of the count as
`done-differently`, with its [FINDINGS.md](../FINDINGS.md) row, when the printed statement
cannot reasonably be proved or proving it adds nothing; or, when only part of the printed
result is formalized, the row is `—` (or is split into its parts, each classed on its own)
until the rest is done. `scripts/check-references.py` holds the note of every `correct` row
to this through a textual proxy: it may not say *done differently*, *no counterpart*, *not
covered*, *stated at `point`*, *only the*, *rather than*, *not the printed*, *not modelled*
or *not transcribed*, unless the note goes on to say, after an explicit `**As printed:**`
marker, why the printed statement follows anyway — a representation that denotes the same
sets, a hypothesis the printed statement has and the proof does not need, a departure in
the proof and not in the statement.

A result out of scope says which of the five reasons above it is:
`restated`, `mathlib`, `not-a-claim`, `done-differently`, `not-covered`. A result
in scope and not yet formalized is `—`.

**A `—` row says what already exists.** Where part of an unformalized result is in the tree,
the third cell is `— partial: <the Lean declarations that exist, linked>; missing: <what is
left>` instead of a bare `—`. The links are checked like any other link (the file has to cite
the paper and the row), but a partial row stays `—` in the count and its class stays `—`.
`scripts/check-references.py` rejects any other text after the dash. A result of which only
a part is formalized is `—` (or is split, each half classed on its own); it is never
`correct` for the half that is there.

**A complexity statement is a row of its own.** A bound printed beside a result
(`complexity O(n⁵)`, `σ = C(p+2, 2) − 1 generators`, `computed in time linear in the formula`)
is not a clause of that result: it gets its own row, `<result> (complexity)` or
`<result> (generators)`, and the result's row states the result alone. The new row is then
sorted by one rule. A **size** (how many generators or constraints the result has) is a
theorem about the result, so it is in scope, `—` or formalized under `Complexity/`. A
**running time** is not: a Lean definition says what is computed and never what computing it
costs, so the tree can only assert it under `Cost/` (CONTRIBUTING.md, "A size is proved; a
running cost is asserted"). A running time is therefore `not-a-claim`, unless the paper
states it as a result in its own right, a Proposition or Theorem whose statement is the bound
(Althoff et al. NAHS'10 `Prop. 10`, `Prop. 11`), and then it is in scope and formalized under
`Cost/` like those two.

## Findings

Formalizing a paper turns things up. Where a printed result is wrong or a proof
does not follow, the paper's own page says so, under its own `## Findings`
heading — beside the result, where someone checking that result will be. These
pages carry one:

<!-- findings -->
* [STL Model Checking of Continuous and Hybrid Systems](2016/roehm-atva-stl-model-checking.md)
* [Ellipsoidal Toolbox (ET)](2006/kurzhanskiy-cdc-ellipsoidal-toolbox.md)
* [Reachability of Uncertain Linear Systems Using Zonotopes](2005/girard-hscc-reachability-zonotopes.md)
* [Taylor Models and Other Validated Functional Inclusion Methods](2003/makino-ijpam-taylor-models.md)
* [Implementation of Taylor Models in CORA 2018](2018/althoff-arch-taylor-models.md)
* [An embedding theorem for spaces of convex sets](1952/radstrom-embedding.md)
* [Reachability Analysis of Nonlinear Systems with Uncertain Parameters using Conservative Linearization](2008/althoff-cdc-conservative-linearization.md)
* [Reachability Analysis and its Application to the Safety Assessment of Autonomous Cars](2010/althoff-thesis.md)
* [Computing Reachable Sets of Hybrid Systems Using a Combination of Zonotopes and Polytopes](2010/althoff-nahs-zonotopes-polytopes.md)
* [Zonotope Bundles for the Efficient Computation of Reachable Sets](2011/althoff-cdc-zonotope-bundles.md)
* [Analyzing Reachability of Linear Dynamic Systems with Parametric Uncertainties](2011/althoff-reachability-parametric-uncertainties.md)
* [Avoiding Geometric Intersection Operations in Reachability Analysis of Hybrid Systems](2012/althoff-hscc-avoiding-intersection.md)
* [Reachability Analysis of Nonlinear Systems using Conservative Polynomialization and Non-Convex Sets](2013/althoff-hscc-conservative-polynomialization.md)
* [On Computing the Minkowski Difference of Zonotopes](2015/althoff-arxiv-minkowski-difference.md)
* [Methods for Order Reduction of Zonotopes](2017/kopetzki-cdc-order-reduction.md)
* [Linear Encodings for Polytope Containment Problems](2019/sadraddini-cdc-polytope-containment.md)
* [Scalable Zonotope-Ellipsoid Conversions using the Euclidean Zonotope Norm](2020/gassmann-acc-zonotope-ellipsoid.md)
* [Utilizing Dependencies to Obtain Subsets of Reachable Sets](2020/kochdumper-hscc-utilizing-dependencies.md)
* [Robust Under-Approximations and Application to Reachability of Non-Linear Control Systems With Disturbances](2020/goubault-lcss-robust-underapproximations.md)
* [Forward Inner-Approximated Reachability of Non-Linear Continuous Systems](2017/goubault-hscc-forward-inner-reachability.md)
* [On the co-NP-Completeness of the Zonotope Containment Problem](2021/kulmburg-ejc-zonotope-containment.md)
* [Sparse Polynomial Zonotopes: A Novel Set Representation for Reachability Analysis](2021/kochdumper-tac-sparse-polyzonotopes.md)
* [Adaptive parameter tuning for reachability analysis of linear systems](2020/wetzlinger-cdc-adaptive-tuning.md)
* [Adaptive Parameter Tuning for Reachability Analysis of Nonlinear Systems](2021/wetzlinger-hscc-adaptive-tuning-nonlinear.md)
* [Adaptive Reachability Algorithms for Nonlinear Systems Using Abstraction Error Analysis](2022/wetzlinger-nahs-abstraction-error.md)
* [Set operations and order reductions for constrained zonotopes](2022/raghuraman-koeln-constrained-zonotopes.md)
* [Scalable Zonotopic Under-approximation of Backward Reachable Sets for Uncertain Linear Systems](2022/yang-lcss-zonotopic-underapproximation.md)
* [Constrained Polynomial Zonotopes](2023/kochdumper-constrained-polyzonotopes.md)
* [Automatic Abstraction Refinement in Neural Network Verification using Sensitivity Analysis](2023/ladner-hscc-abstraction-refinement.md)
* [Fully Automatic Neural Network Reduction for Formal Verification](2023/ladner-tmlr-network-reduction.md)
* [Backward Reachability Analysis of Perturbed Continuous-Time Linear Systems Using Set Propagation](2023/wetzlinger-arxiv-backward-reachability.md)
* [Fully-Automated Verification of Linear Systems Using Inner- and Outer-Approximations of Reachable Sets](2023/wetzlinger-fully-automated-verification.md)
* [Fully-Automated Verification of Linear Systems Using Reachability Analysis with Support Functions](2023/wetzlinger-hscc-support-functions.md)
* [Search-based and Stochastic Solutions to the Zonotope and Ellipsotope Containment Problems](2024/kulmburg-ecc-zonotope-ellipsotope-containment.md)
* [Exponent Relaxation of Polynomial Zonotopes and Its Applications in Formal Neural Network Verification](2024/ladner-aaai-exponent-relaxation.md)
* [Implementation of Polyhedral Operations in CORA 2024](2024/wetzlinger-arch-polyhedral-operations.md)
* [Zonotopic guaranteed state estimation for uncertain systems](2013/le-automatica-zonotopic-estimation.md)
* [Set-membership approach and Kalman observer based on zonotopes for discrete-time descriptor systems](2018/wang-automatica-descriptor-observer.md)
* [Guarantees for Real Robotic Systems: Unifying Formal Controller Synthesis and Reachset-Conformant Identification](2023/liu-tro-guarantees-real-robotic.md)
* [Checking and Establishing Reachset Conformance in CORA 2023](2023/althoff-arch-reachset-conformance.md)
* [Reachset-Conformant System Identification](2026/luetzow-tac-reachset-conformant-identification.md)
* [Explaining Fast and Slow: Abstraction and Refinement of Provable Explanations](2025/bassan-icml-explaining-fast-and-slow.md)
* [Formal Verification of Graph Convolutional Networks with Uncertain Node Features and Uncertain Graph Structure](2025/ladner-tmlr-gcn.md)
* [Reachability Analysis for Hybrid Systems with Nonlinear Guard Sets](2020/kochdumper-hscc-nonlinear-guards.md)
* [Safety Assessment for Stochastic Linear Systems using Enclosing Hulls of Probability Density Functions](2009/althoff-ecc-enclosing-hulls.md)
* [Reachability Analysis of ARMAX Models](2023/luetzow-cdc-armax.md)
* [Inner Approximations of Reachable Sets for Nonlinear Systems using the Minkowski Difference](2024/wetzlinger-lcss-inner-minkowski-difference.md)
* [Reachability Analysis of Large Linear Systems with Uncertain Inputs in the Krylov Subspace](2020/althoff-tac-krylov.md)
* [Reachability Analysis of Nonlinear Differential-Algebraic Systems](2014/althoff-tac-nonlinear-dae.md)
* [Implementation of Interval Arithmetic in CORA 2016](2017/althoff-arch-interval-arithmetic.md)
* [Guaranteed State Estimation in CORA 2021](2021/althoff-arch-state-estimation.md)
* [General Inner Approximation of Vector-valued Functions](2013/mullier-rc-general-inner-approximation.md)
* [Zono-Conformal Prediction: Zonotope-Based Uncertainty Quantification for Regression and Classification Tasks](2025/luetzow-jmlr-zono-conformal-prediction.md)
* [Robust Identification of Hybrid Automata from Noisy Data](2025/kochdumper-hscc-hybrid-automata-identification.md)
* [Interval estimation methods for discrete-time linear time-invariant systems](2019/tang-tac-interval-estimation.md)
* [Zonotopic set-membership state estimation for discrete-time descriptor LPV systems](2019/wang-tac-descriptor-lpv-estimation.md)
* [AI2: Safety and Robustness Certification of Neural Networks with Abstract Interpretation](2018/gehr-sp-ai2.md)
* [Fast and Effective Robustness Certification](2018/singh-neurips-deepz.md)
* [Dynamic mode decomposition with control](2016/proctor-siads-dmd-control.md)
* [Discovering governing equations from data by sparse identification of nonlinear dynamical systems](2016/brunton-pnas-sindy.md)
* [A Box-Consistency Contractor Based on Extremal Functions](2010/trombettoni-cp-box-consistency.md)
* [On the Hyperbox – Hyperplane Intersection Problem](2009/lara-infocomp-hyperbox-hyperplane.md)
* [Model Predictive Control with Signal Temporal Logic Specifications](2014/raman-cdc-mpc-stl.md)
* [Benchmarks for the Formal Verification of Power Systems](2022/althoff-arch-power-systems.md)
* [Zonotopic Fault Detection Observer with H− Performance](2017/wang-ccc-fault-detection-observer.md)
* [A distributed set-membership approach based on zonotopes for interconnected systems](2018/wang-cdc-distributed-set-membership.md)
* [Set-Based Training for Neural Network Verification](2025/koller-tmlr-set-based-training.md)
* [Goffin's algorithm for zonotopes](2012/cerny-kybernetika-goffin-zonotopes.md)
* [On the parameterized computation of minimum volume outer ellipsoid of Minkowski sum of ellipsoids](2018/halder-cdc-minkowski-sum-ellipsoids.md)
* [Distributed Set-Based Observers Using Diffusion Strategies](2023/alanwar-jfi-diffusion-observers.md)
* [Approximability of the Containment Problem for Zonotopes and Ellipsotopes](2025/kulmburg-tac-approximability-containment.md)

[FINDINGS.md](../FINDINGS.md) is the other half, and stays at the root: the
places this formalization parts from CORA on purpose, which belong to no paper.

## Citing

Cite as the papers are cited in the source — `[1]`, or `[1, Prop. 3.1]` — and see
[CONTRIBUTING.md](../CONTRIBUTING.md#references) for what belongs in a `##
References` block. [FINDINGS.md](../FINDINGS.md) records where a source turned
out to be wrong; the row for such a result says so and points there.
