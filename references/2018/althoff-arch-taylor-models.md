# Implementation of Taylor Models in CORA 2018

M. Althoff, D. Grebenyuk, and N. Kochdumper. "Implementation of Taylor Models in CORA 2018". In Proc. of the 5th International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH18), EPiC Series in Computing, vol. 54, pp. 145-173, 2018.

**Source:** https://easychair.org/publications/paper/9Tz3 (the EPiC PDF, 29 pages, pp. 145-173, read in full; text extracted with `pypdf`. The TUM repository copy <https://mediatum.ub.tum.de/doc/1454477/file.pdf> is the same file. Over- and underlines are lost in the extraction, so the listing's `α̅`/`α̲` and the two ends in line 31 of `Alg. 1` are read from their comments.)  
**Inventory:** confirmed (the numbered items are Definitions 1-2, Algorithm 1, Examples 1-5, equations (1)-(38) and Tables 1-8; Appendix A lists the elementary functions as eqs. (21)-(32), Appendix B the improved inverse as eqs. (33)-(38))

The tool paper of CORA's `@taylm` (and its `zoo` and affine arithmetic). Most of its Taylor
model arithmetic restates [Makino and Berz 2003](../2003/makino-ijpam-taylor-models.md), which it
cites for each formula; those rows defer to that page. What is its own: interval evaluation of a
polynomial over a box (eq. 12), branch and bound (`Alg. 1`, CORA's `optBnb` and `optBnbAdv`),
`tan` and `tanh` as quotients, and the improved remainder of the inverse (Appendix B). Affine
arithmetic (Sec. 3) and the `zoo` class (Sec. 4.4) have no numbered results.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Def. 1` | (Taylor polynomial) `P^q(x - x₀) = Σ_{l ∈ L_q} Πᵢ (xᵢ - x₀,ᵢ)^{lᵢ}/lᵢ! · ∂^{l₁+…+lₙ}f/∂x₁^{l₁}…∂xₙ^{lₙ}(x₀)` over the multi-indices `L_q` of total order at most `q` (eq. 1). | n/a — restated from Neidinger's "Directions for computing truncated multivariate Taylor series" (Sec. 3), which has no page here; `Taylm.taylorPoly` is the coordinate-free form | `restated` |
| `Def. 2` | (Taylor model) `f` `q + 1` times continuously differentiable near `[x]`, `P^q` its Taylor polynomial at `x₀ ∈ [x]`, and `[I]` with `f(x) ∈ P^q(x - x₀) + [I]` on `[x]` (eq. 2): `(P^q, I)` is a `q`-th order Taylor model. | n/a — restated; tracked as `Def. 1` on [Makino and Berz 2003](../2003/makino-ijpam-taylor-models.md) | `restated` |
| `Eq. 3` | Interval `+`, `-`, `·` and `/`, the reciprocal of an interval containing `0` as `∅`, a half-line or the whole line. | n/a — restated from Althoff and Grebenyuk's CORA 2016 interval paper, which has no page here | `restated` |
| `Eq. 4` | `[x] - [x] = [x̲ - x̅, x̅ - x̲] ≠ 0`: the dependency problem. | n/a — an illustration | `not-a-claim` |
| `Eq. 5` | `B(P^q(x - x₀)) = [min_{x∈[x]} P^q, max_{x∈[x]} P^q]`, "returning an over-approximation of the exact bounds"; `B(T) = B(P) + [I]`. | [`Bounds.lean`](../../src/CORALean/ContSet/Taylm/Real/Operations/Bounds.lean), [`BoundsMem.lean`](../../src/CORALean/ContSet/Taylm/Real/Theorems/BoundsMem.lean) — `B` as an over-approximation, interval evaluation over the normalized box: the enclosed function stays in `B(T)` | `underspecified` — the equation prints the exact range, the text and every use an over-approximation |
| `Eq. 6` | `αT₁ + βT₂ = (αP₁ + βP₂, α[I₁] + β[I₂])`. | [`Smul.lean`](../../src/CORALean/ContSet/Taylm/Real/Operations/Smul.lean), [`SmulOuter.lean`](../../src/CORALean/ContSet/Taylm/Real/Theorems/SmulOuter.lean), [`Plus.lean`](../../src/CORALean/ContSet/Taylm/Real/Operations/Plus.lean), [`PlusOuter.lean`](../../src/CORALean/ContSet/Taylm/Real/Theorems/PlusOuter.lean) — `(T₁.smul α).plus (T₂.smul β)` is that model, and encloses `αf + βg` | `correct` |
| `Eq. 7` | `αT₁ - βT₂ = (αP₁ - βP₂, α[I₁] - β[I₂])`. | [`Smul.lean`](../../src/CORALean/ContSet/Taylm/Real/Operations/Smul.lean), [`SmulOuter.lean`](../../src/CORALean/ContSet/Taylm/Real/Theorems/SmulOuter.lean), [`Minus.lean`](../../src/CORALean/ContSet/Taylm/Real/Operations/Minus.lean), [`MinusOuter.lean`](../../src/CORALean/ContSet/Taylm/Real/Theorems/MinusOuter.lean) | `correct` |
| `Eq. 8` | `T₁·T₂ = (P_r, B(P_c) + B(P₁)·I₂ + B(P₂)·I₁ + I₁·I₂)`. | n/a — restated; tracked as `Def. 2` on [Makino and Berz 2003](../2003/makino-ijpam-taylor-models.md) | `restated` |
| `Eq. 9` | `T₁/T₂ = T₁·(1/T₂)`. | [`Rdivide.lean`](../../src/CORALean/ContSet/Taylm/Real/Operations/Rdivide.lean), [`RdivideOuter.lean`](../../src/CORALean/ContSet/Taylm/Real/Theorems/RdivideOuter.lean) — encloses `f/g` under the inverse's condition on `T₂` | `correct` |
| `Eq. 10` | `1/T = (1/c_f)[1 - T̃/c_f + … + (-1)^q T̃^q/c_f^q] + (-1)^{q+1} B(T̃)^{q+1}/(c_f^{q+2}(1 + [0, 1]·B(T̃)/c_f)^{q+2})`. | n/a — restated; tracked as `Def. 3 (inverse)` on [Makino and Berz 2003](../2003/makino-ijpam-taylor-models.md) | `restated` |
| `Eq. 11` | An interval `[a]` as the Taylor model `0.5(a̅ + a̲) + 0.5(a̅ - a̲)x + [0, 0]`, `x ∈ [-1, 1]`. | [`IntervalTaylmExact.lean`](../../src/CORALean/ContSet/Conversion/Real/Theorems/IntervalTaylmExact.lean) — `Interval.taylm`; its range is the box (`taylm_exact`) | `correct` |
| `Eq. 12` | `B(P(x, y)) ⊆ Σᵢ Σⱼ c_{i,j} [x̲, x̅]ⁱ [y̲, y̅]ʲ`: interval evaluation bounds a polynomial over a box. | [`PowBounds.lean`](../../src/CORALean/ContSet/Taylm/Real/Operations/PowBounds.lean), [`ProdBounds.lean`](../../src/CORALean/ContSet/Taylm/Real/Operations/ProdBounds.lean), [`TermBoxBounds.lean`](../../src/CORALean/ContSet/Taylm/Real/Operations/TermBoxBounds.lean), [`PolyBoxBounds.lean`](../../src/CORALean/ContSet/Taylm/Real/Operations/PolyBoxBounds.lean), [`PolyBoxBoundsMem.lean`](../../src/CORALean/ContSet/Taylm/Real/Theorems/PolyBoxBoundsMem.lean) — any number of variables, any box | `correct` |
| `Example 1` | `r = 0.1x³ - 0.5x² + 1` on `[0, 6]`: interval evaluation gives `[-17.0, 22.6]`, of the normalized form `2.7x̃³ + 3.6x̃² - 0.9x̃ - 0.8` `[-4.4, 6.4]`. | n/a — a worked example | `not-a-claim` |
| `Example 2` | Branch and bound on the same function: `[-3.50, 5.50]`, `[-2.15, 5.05]`, `[-1.25, 1.91]` after three iterations. | n/a — a worked example | `not-a-claim` |
| `Alg. 1` | (Branch and bound) From `[x]` bounded by eq. (12), repeatedly halve along its widest coordinate the box holding the upper bound and the box holding the lower bound (one box if they coincide), re-expanding `P` at the halves' centers in the advanced setting, until neither end of the union of the boxes' intervals moves by more than `2ε·rad([r∪])`; return the union. | [`Box.lean`](../../src/CORALean/ContSet/Taylm/Real/Definitions/Box.lean), [`ArgMaxIdx.lean`](../../src/CORALean/ContSet/Taylm/Real/Operations/ArgMaxIdx.lean), [`WidestCoord.lean`](../../src/CORALean/ContSet/Taylm/Real/Operations/WidestCoord.lean), [`HalveBox.lean`](../../src/CORALean/ContSet/Taylm/Real/Operations/HalveBox.lean), [`SplitAt.lean`](../../src/CORALean/ContSet/Taylm/Real/Operations/SplitAt.lean), [`ListMin.lean`](../../src/CORALean/ContSet/Taylm/Real/Operations/ListMin.lean), [`ListMax.lean`](../../src/CORALean/ContSet/Taylm/Real/Operations/ListMax.lean), [`BnbStep.lean`](../../src/CORALean/ContSet/Taylm/Real/Operations/BnbStep.lean), [`BnbLoop.lean`](../../src/CORALean/ContSet/Taylm/Real/Operations/BnbLoop.lean), [`BnbLoopMem.lean`](../../src/CORALean/ContSet/Taylm/Real/Theorems/BnbLoopMem.lean), [`ReexpTerms.lean`](../../src/CORALean/ContSet/Taylm/Real/Operations/ReexpTerms.lean), [`ReexpBoxBounds.lean`](../../src/CORALean/ContSet/Taylm/Real/Operations/ReexpBoxBounds.lean), [`Reexpand.lean`](../../src/CORALean/ContSet/Taylm/Real/Operations/Reexpand.lean), [`BranchAndBound.lean`](../../src/CORALean/ContSet/Taylm/Real/Operations/BranchAndBound.lean), [`BranchAndBoundMem.lean`](../../src/CORALean/ContSet/Taylm/Real/Theorems/BranchAndBoundMem.lean), [`OptBnb.lean`](../../src/CORALean/ContSet/Taylm/Real/Operations/OptBnb.lean), [`OptBnbMem.lean`](../../src/CORALean/ContSet/Taylm/Real/Theorems/OptBnbMem.lean), [`OptBnbAdv.lean`](../../src/CORALean/ContSet/Taylm/Real/Operations/OptBnbAdv.lean), [`OptBnbAdvMem.lean`](../../src/CORALean/ContSet/Taylm/Real/Theorems/OptBnbAdvMem.lean) — the listing's lines as `let`s, both settings; the `repeat` bounded by `fuel`; sound for any `ε` and any number of iterations, the boxes always covering `[x]` | `correct` |
| `Sec. 2.3.3` | (Linear Dominated Bounder and Quadratic Fast Bounder) Iteratively eliminate sub-boxes that cannot hold the minimum or maximum, guided by the linear and quadratic parts, until one sub-box is left for each. | n/a — restated; tracked as `Sec. 2` on [Makino and Berz 2005](../2005/makino-tc-global-optimization.md), whose `Sec. 3` is the QFB | `restated` |
| `Eq. 13` | (Sherman-Morrison) `(A + B)⁻¹ = A⁻¹ - (A⁻¹BA⁻¹)/(1 + tr(A⁻¹B))`, "when `B` has unitary rank". | n/a — Mathlib's `Matrix.add_mul_mul_inv_eq_sub` (Woodbury), whose rank-one case this is; it also needs `A` and `1 + tr(A⁻¹B)` invertible, which the printed condition leaves out | `mathlib` |
| `Eq. 14` | `(c_f + T̃)⁻¹ = c_f⁻¹ - (c_f⁻¹T̃c_f⁻¹)/(1 + tr(c_f⁻¹T̃))` for `T̃` of rank one, applied column by column to invert a matrix of Taylor models. | n/a — eq. (13) at `A = c_f`, Mathlib's | `mathlib` |
| `Eq. 15–18` | CORA's polynomial representation `{c, E, id}` (coefficients, exponent matrix, variable names), by example, and the common representation of two polynomials. | n/a — a data layout | `not-a-claim` |
| `Eq. 19` | `max_order`, `tolerance` and `eps` of a sum or product: the larger order, the smaller tolerance and `eps`. | n/a — bookkeeping conventions of the class | `not-a-claim` |
| `Example 3` | `sin([0, π/2])`: interval arithmetic exact, affine arithmetic `[-0.1567, 1.2624]`, a third-order Taylor model `[-0.1234, 1.3354]`. | n/a — a worked example | `not-a-claim` |
| `Example 4` | `√(x³ - x)` on `[2, 3]`: interval arithmetic best, affine arithmetic better than Taylor models. | n/a — a worked example | `not-a-claim` |
| `Example 5` | `0.1x³ - 0.5x² + 1` on `[0, 6]`: Taylor models best. | n/a — a worked example | `not-a-claim` |
| `Eq. 20` | The relative precision `[δ̲, δ̅]` of an interval against a reference. | n/a — an experimental metric | `not-a-claim` |
| `Table 1` | The mathematical methods of `taylm`. | n/a — a list of methods | `not-a-claim` |
| `Table 2` | The auxiliary methods of `taylm`. | n/a — a list of methods | `not-a-claim` |
| `Table 3` | Precision of CORA's bounders and Flow* (part 1). | n/a — experiments | `not-a-claim` |
| `Table 4` | Precision of CORA's bounders and Flow* (part 2). | n/a — experiments | `not-a-claim` |
| `Table 5` | Execution times of the Taylor model bounders and Flow*. | n/a — experiments | `not-a-claim` |
| `Table 6` | Precision of affine arithmetic in CORA and INTLAB. | n/a — experiments | `not-a-claim` |
| `Table 7` | Execution times of affine arithmetic in CORA and INTLAB. | n/a — experiments | `not-a-claim` |
| `Table 8` | The benchmarks' input ranges. | n/a — experimental setup | `not-a-claim` |
| `Eq. 21` | `exp(T)`, with the Lagrange term `exp(c_f)/(q+1)!·B(T̃^{q+1})·exp([0, 1]·B(T̃))`. | n/a — restated from Makino and Berz's eqs. (2.2)-(2.4) with the power bounded after it is taken; tracked as `Def. 3 (exp)` on [Makino and Berz 2003](../2003/makino-ijpam-taylor-models.md) | `restated` |
| `Eq. 22` | `log(T)` under `B(T) ⊂ (0, ∞)`. | n/a — restated; tracked as `Def. 3 (log)` on [Makino and Berz 2003](../2003/makino-ijpam-taylor-models.md) | `restated` |
| `Eq. 23` | `√T` under `B(T) ⊂ (0, ∞)`. | n/a — restated; tracked as `Def. 3 (sqrt)` on [Makino and Berz 2003](../2003/makino-ijpam-taylor-models.md) | `restated` |
| `Eq. 24` | `sin(T)`, `J` by `q mod 4`. | n/a — restated; tracked as `Def. 3 (sin)` on [Makino and Berz 2003](../2003/makino-ijpam-taylor-models.md) | `restated` |
| `Eq. 25` | `cos(T)`, `J` by `q mod 4`. | n/a — restated; tracked as `Def. 3 (cos)` on [Makino and Berz 2003](../2003/makino-ijpam-taylor-models.md) | `restated` |
| `Eq. 26` | `tan(T) = sin(T)·(1/cos(T))`. | [`SinRdivideCosOuter.lean`](../../src/CORALean/ContSet/Taylm/Real/Theorems/SinRdivideCosOuter.lean) — encloses `tan ∘ f` whenever `cos(T)` passes the inverse's condition | `correct` |
| `Eq. 27` | `sinh(T)`. | n/a — restated; tracked as `Def. 3 (sinh)` on [Makino and Berz 2003](../2003/makino-ijpam-taylor-models.md) | `restated` |
| `Eq. 28` | `cosh(T)`. | n/a — restated; tracked as `Def. 3 (cosh)` on [Makino and Berz 2003](../2003/makino-ijpam-taylor-models.md) | `restated` |
| `Eq. 29` | `tanh(T) = sinh(T)/cosh(T)`. | [`SinhRdivideCoshOuter.lean`](../../src/CORALean/ContSet/Taylm/Real/Theorems/SinhRdivideCoshOuter.lean) — encloses `tanh ∘ f` whenever `cosh(T)` passes the inverse's condition | `correct` |
| `Eq. 30` | `arcsin(T) = arcsin(c_f) + G + G³/3! + …` under `B(T) ⊂ (-1, 1)`, `G = T√(1 - c_f²) - c_f√(1 - T²)`, `arcsin^{(q)}(0) = (q-2)² arcsin^{(q-2)}(0)`. | n/a — restated, with the addition formula's missing condition; tracked as `Def. 3 (arcsin)` on [Makino and Berz 2003](../2003/makino-ijpam-taylor-models.md) | `restated` |
| `Eq. 31` | `arccos(T) = π/2 - arcsin(T)`. | n/a — restated; tracked as `Def. 3 (arccos)` on [Makino and Berz 2003](../2003/makino-ijpam-taylor-models.md) | `restated` |
| `Eq. 32` | `arctan(T) = arctan(c_f) + G - G³/3 + …`, `G = (T - c_f)/(1 + c_f T)`. | n/a — restated, with the addition formula's missing condition; tracked as `Def. 3 (arctan)` on [Makino and Berz 2003](../2003/makino-ijpam-taylor-models.md) | `restated` |
| `Eq. 33` | The Lagrange remainder `L_q(B(T̃), c_f)` of `1/T`, eq. (10)'s last term. | n/a — restated; tracked as `Def. 3 (inverse)` on [Makino and Berz 2003](../2003/makino-ijpam-taylor-models.md) | `restated` |
| `Eq. 34` | The exact remainder `R_q(x, c_f) = ∫_{c_f}^x f^{(q+1)}(t)(x - t)^q/q! dt`, `f(x) = 1/x`. | n/a — Taylor's theorem with integral remainder, Mathlib's `taylor_integral_remainder` | `mathlib` |
| `Eq. 35` | `T = 0.45 + 0.35x`: `1/B(T) = [1.25, 10]` but `L₆ = [-64339.29688, 64339.29688]`. | n/a — a worked example | `not-a-claim` |
| `Eq. 36–37` | `R_q(x, c_f) = a/(q+1)·(x - c_f)^q/c_f^{q+1} - q/(q+1)·R_{q-1}(x, c_f)`, `a = (q+1)(-1)^{q+1}`, from `R₀(x, c_f) = a/c_f - a/x`, by integration by parts. | [`InvRemS.lean`](../../src/CORALean/ContSet/Taylm/Real/Operations/InvRemS.lean), [`InvRemSEq.lean`](../../src/CORALean/ContSet/Taylm/Real/Theorems/InvRemSEq.lean) — the recursion on `Sⱼ = ∫_c^x (x-t)ʲ/tʲ⁺² dt`, and `a·S_q` is the exact remainder `1/x - Σₖ₌₀^q (-1)ᵏ(x-c)ᵏ/cᵏ⁺¹` | `underspecified` — `R_{q-1}` there is `a·∫(x-t)^{q-1}/t^{q+1}` with the top order's `a`, not eq. (34) at order `q - 1` |
| `Eq. 38` | (Heuristic) `rem = L_q(B(T̃), c_f)` if `L_q ⊂ 1/B(T)`, otherwise `R_q(B(T), c_f)`. | [`InvSubSumEq.lean`](../../src/CORALean/ContSet/Taylm/Real/Theorems/InvSubSumEq.lean), [`InvTight.lean`](../../src/CORALean/ContSet/Taylm/Real/Operations/InvTight.lean), [`InvTightOuter.lean`](../../src/CORALean/ContSet/Taylm/Real/Theorems/InvTightOuter.lean) — CORA's test (`R_q` once `L_q` reaches past `1/B(T)` at both ends); both remainders in magnitude, `R_q` from its closed form; sound in either branch | `underspecified` — as printed the test never passes, `1/B(T)` excluding `0` and `L_q` holding it |

## Findings

**`Eq. 5` prints the exact range where it means a bound.** `B(P) = [min P, max P]` is the exact
range, but the same sentence says `B` returns "an over-approximation of the exact bounds", and
every use (interval evaluation, branch and bound, LDB/QFB) computes one. Formalized as the
over-approximation: `bounds_mem` says the range lies in `B`, not that `B` is the range.

**`Eq. 36–37`'s `R_{q-1}` is not eq. (34) at order `q - 1`.** Integration by parts gives
`R_q = a/(q+1)·(x - c)^q/c^{q+1} - a·q/(q+1)·∫_c^x (x - t)^{q-1}/t^{q+1} dt`, and the paper writes
the integral term as `q/(q+1)·R_{q-1}`. With `R_{q-1}` as eq. (34) defines it, whose prefactor is
`q(-1)^q` and not `a = (q+1)(-1)^{q+1}`, the recursion is false: at `c = 1`, `x = 2`, `q = 1` the
remainder `R₁ = 1/2 - 1 + 1 = 1/2`, while the printed right side is `1 - (1/2)(-1/2) = 5/4`. Read
with `a` fixed at the top order, `R_j := a∫_c^x (x - t)^j/t^{j+2} dt`, it holds, and eq. (37)'s
`R₀ = a/c - a/x` is that reading. CORA's `priv_inverse` computes exactly this: the recursion on
the integrals and one multiplication by `a` at the end; `invRemS_eq` proves `a·S_q` is the exact
remainder.

**`Eq. 38`'s test never passes.** `1/B(T)` is the range of `1/T`, which excludes `0`, while the
remainder `L_q` contains `0`; so `L_q ⊂ 1/B(T)` is never true, and as printed the heuristic always
takes the slower exact remainder. CORA's `priv_inverse` tests instead whether `L_q` reaches past
`1/B(T)` at both ends, and takes the exact remainder only then, which matches the text's intent
(the Lagrange remainder "does not always result in large over-approximations"). Formalized with
CORA's test; both branches are sound, so the choice affects only how tight the result is.

## Cited without a result

These name the paper as a whole. A locator would put each in a row above.

* [`Zoo.lean`](../../src/CORALean/ContSet/Zoo/Real/Zoo.lean)
* [`Zoo.lean`](../../src/CORALean/ContSet/Zoo/Float/Zoo.lean)
