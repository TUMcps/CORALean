# Implementation of Interval Arithmetic in CORA 2016

M. Althoff and D. Grebenyuk. "Implementation of Interval Arithmetic in CORA 2016". In Proc. of the 3rd International Workshop on Applied Verification for Continuous and Hybrid Systems (ARCH16), EPiC Series in Computing, vol. 43, pp. 91-105, 2017.

**Source:** https://easychair.org/publications/open/ZRJ (the EPiC PDF, 15 pages, pp. 91-105, read in full; text extracted with `pypdf`; the volume is dated 2017, the workshop ARCH16). Over- and underlines are lost in the extraction, so which bound is the infimum and which the supremum in eqs. (1)-(15) is read from the monotonicity each case states, and checked against the formalization, which proves it.  
**Inventory:** confirmed (the numbered items are Proposition 1, equations (1)-(18), Figures 1-4 and Tables 1-3; Sec. 2 and Sec. 3 also state the center-radius form, the interval hull and the elementwise unary operations in prose)

The tool paper of CORA's `@interval`, which CORA's `sin`, `cos` and `tan` cite. It evaluates
every elementary function on an interval by monotone pieces, as the exact range
`f([x]) = {f(x) | x ∈ [x]}`, rounding ignored. The non-periodic functions (eqs. 4-10) are
CORALean's `Interval` operations, proved exact; their `NaN` branches, for an argument partly or
wholly outside the domain, signal an improper input and claim no range. The periodic ones
(eqs. 11-15, Prop. 1) are written here as printed, case by case: CORA's own `sin` and `cos` have
since moved to `cos(I - π/2)` and a largest-cosine search, and its `tan` to a test on the end
values, so the paper's cases are formalized as their own definitions, not through CORA's.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Sec. 2` | An interval is `[x] = mid([x]) ⊕ rad([x]) ⊗ [-1, 1]`, with `mid([x]) = 0.5(x̲ + x̅)` and `rad([x]) = 0.5(x̅ - x̲)`. | [`CenterAddRadius.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/CenterAddRadius.lean), [`CenterSubRadius.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/CenterSubRadius.lean), [`MemOfCenterRadius.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/MemOfCenterRadius.lean) — `mid ± rad` are the ends, and `x` is in the interval of center `c` and radius `r` exactly when `\|x - c\| ≤ r` | `correct` |
| `Eq. 1` | `[x] ∩ [y] = [max(x̲, y̲), min(x̅, y̅)]` if `max(x̲, y̲) ≤ min(x̅, y̅)`, else `∅`; `[x] ∪ [y] = [min(x̲, y̲), max(x̅, y̅)]` under the same condition, else `[NaN, NaN]`; the interval hull is `[min(x̲, y̲), max(x̅, y̅)]` always. | [`IntersectionExact.lean`](../../src/CORALean/ContSet/Interval/Real/Operations/IntersectionExact.lean), [`Or.lean`](../../src/CORALean/ContSet/Interval/Real/Operations/Or.lean) — the intersection exactly, a crossed result denoting `∅`; the hull is `Interval.or`; that two meeting intervals' union is their hull is Mathlib's `Set.Icc_union_Icc'`. `[NaN, NaN]` signals a union that is no interval and claims nothing | `correct` |
| `Eq. 2` | `[x] + [y] = [x̲ + y̲, x̅ + y̅]`, `[x] - [y] = [x̲ - y̅, x̅ - y̲]`, `[x] · [y] = [min(x̲y̲, x̲y̅, x̅y̲, x̅y̅), max(…)]`, each the set `{x ∘ y \| x ∈ [x], y ∈ [y]}`. | [`PlusExact.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/PlusExact.lean), [`MinusExact.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/MinusExact.lean), [`TimesExact.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/TimesExact.lean) — exact, for nonempty operands | `correct` |
| `Eq. 3` | `[x]/[y] = [x] · (1/[y])`, with `1/[y]` `∅` at `[0, 0]`, `[1/y̅, 1/y̲]` if `0 ∉ [y]`, `[1/y̅, ∞[` if `y̲ = 0 < y̅`, `]-∞, 1/y̲]` if `y̲ < 0 = y̅`, `]-∞, ∞[` if `y̲ < 0 < y̅`. | [`InvImageIccCases.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/InvImageIccCases.lean), [`RdivideExact.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/RdivideExact.lean) — `{1/y \| y ∈ [y], y ≠ 0}` is each of the first four exactly, and in the fifth unbounded both ways, so `]-∞, ∞[` is its interval hull (the set itself is `]-∞, 1/y̲] ∪ [1/y̅, ∞[`); the quotient exact on boxes away from `0` | `correct` |
| `Eq. 4` | `e^[x] = [e^x̲, e^x̅]`. | [`ExpExact.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/ExpExact.lean) | `correct` |
| `Eq. 5` | `log([x]) = [log x̲, log x̅]` if `x̲ ≥ 0`, `[NaN, log x̅]` if `x̲ < 0 ≤ x̅`, `[NaN, NaN]` if `x̅ < 0`; `√[x]` alike. | [`LogExact.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/LogExact.lean), [`SqrtExact.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/SqrtExact.lean) — the first case, exactly; for `log` at `x̲ > 0`, `x̲ = 0` reading `log 0 = -∞`, the extended-real infimum of the range on `(0, x̅]`. The `NaN` cases mark an improper argument and claim no range | `correct` |
| `Eq. 6` | `arcsin`, `arccos` by their ends on `[-1, 1]` (`arccos` swapping them), `NaN` for an end outside; `arctan([x]) = [arctan x̲, arctan x̅]`. | [`AsinExact.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/AsinExact.lean), [`AcosExact.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/AcosExact.lean), [`AtanExact.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/AtanExact.lean) — the in-domain cases, exactly | `correct` |
| `Eq. 7` | `sinh`, `tanh` by their ends; `cosh([x])` is `[cosh x̅, cosh x̲]` for `x̅ < 0`, `[1, cosh(max(\|x̲\|, \|x̅\|))]` across `0`, `[cosh x̲, cosh x̅]` for `x̲ > 0`. | [`SinhExact.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/SinhExact.lean), [`CoshExact.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/CoshExact.lean), [`TanhExact.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/TanhExact.lean) | `correct` |
| `Eq. 8` | `arcsinh` by its ends; `arccosh` on `[1, ∞[` and `arctanh` on `]-1, 1[` by their ends, `NaN` for an end outside. | [`AsinhExact.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/AsinhExact.lean), [`AcoshExact.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/AcoshExact.lean), [`AtanhExact.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/AtanhExact.lean) — the in-domain cases, exactly | `correct` |
| `Eq. 9` | `[x]ⁿ` for `n ∈ ℕ`: `[x̲ⁿ, x̅ⁿ]` if `x̲ > 0` or `n` odd, `[x̅ⁿ, x̲ⁿ]` if `x̅ < 0` and `n` even, `[0, max(\|x̲\|, \|x̅\|)ⁿ]` if `0 ∈ [x]` and `n` even. | [`PowerExact.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/PowerExact.lean) — every case, exactly, for every `n ≥ 1`; `ℕ` is read without `0`, where the third case would give `[0, 1]` for the range `{1}`, and `Interval.power` exempts `n = 0` from it | `correct` |
| `Eq. 10` | `\|[x]\|` is `[\|x̅\|, \|x̲\|]` if `x̅ < 0`, `[x̲, x̅]` if `x̲ > 0`, `[0, max(\|x̲\|, \|x̅\|)]` if `0 ∈ [x]`. | [`AbsExact.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/AbsExact.lean) | `correct` |
| `Eq. 11` | The bounds reduced into `[0, 2π)`: `y̲ = mod(x̲, 2π)`, `y̅ = mod(x̅, 2π)`. | [`SinByRegions.lean`](../../src/CORALean/ContSet/Interval/Real/Operations/SinByRegions.lean), [`CosByRegions.lean`](../../src/CORALean/ContSet/Interval/Real/Operations/CosByRegions.lean) — the first two steps of both, MATLAB's `mod`, `x - 2π⌊x/2π⌋` | `correct` |
| `Prop. 1` | For `x̅ - x̲ < 2π`, after (11) either `x̅ - x̲ = y̅ - y̲` or `x̅ - x̲ = (y̅ - y̲) + 2π`. | [`ModSubModCases.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/ModSubModCases.lean) — for any period, with the first case exactly when `y̲ ≤ y̅`, the test the text derives from it | `correct` |
| `Eq. 12` | `sin([x])` in twelve cases by the regions `R_s1 = [0, π/2[`, `R_s2 = [π/2, 3π/2[`, `R_s3 = [3π/2, 2π[` of `y̲`, `y̅` and whether `y̲ > y̅`; `[-1, 1]` if `x̅ - x̲ ≥ 2π`. | [`SinByRegions.lean`](../../src/CORALean/ContSet/Interval/Real/Operations/SinByRegions.lean), [`SinByRegionsExact.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/SinByRegionsExact.lean) — the printed cases in the printed order; each is the sine's range on `[x̲, x̅]`, exactly | `correct` |
| `Eq. 13` | `cos([x])` in six cases by the regions `R_c1 = [0, π[`, `R_c2 = [π, 2π[`. | [`CosByRegions.lean`](../../src/CORALean/ContSet/Interval/Real/Operations/CosByRegions.lean), [`CosByRegionsExact.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/CosByRegionsExact.lean) — each case the cosine's range, exactly | `correct` |
| `Eq. 14` | `tan([x])`, with `z = mod(x, π)` and regions `R_t1 = [0, π/2[`, `R_t2 = [π/2, π[`: `]-∞, ∞[` if `x̅ - x̲ ≥ π`, or `z̲ > z̅` within one region, or `z̲ ∈ R_t1`, `z̅ ∈ R_t2`; `[tan z̲, tan z̅]` if `z̲ ≤ z̅` within one region ("6 cases as for `cos`"). | [`TanByRegions.lean`](../../src/CORALean/ContSet/Interval/Real/Operations/TanByRegions.lean), [`TanByRegionsExact.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/TanByRegionsExact.lean), [`TanUnboundedOfPole.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/TanUnboundedOfPole.lean), [`ModSubModCases.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/ModSubModCases.lean) — with the missing case `z̲ ∈ R_t2`, `z̅ ∈ R_t1` as `[tan z̲, tan z̅]` and both ends off the poles: a finite answer is the range (poles left out) exactly, `]-∞, ∞[` is returned exactly when a pole is inside, where the range is unbounded both ways | `underspecified` — one of the six cases is not printed, and at an end on a pole the formula is not the range |
| `Eq. 15` | `cot([x]) = ]-∞, ∞[` if `x̅ - x̲ ≥ π` or `z̲ > z̅`, `[cot z̅, cot z̲]` if `z̲ ≤ z̅`. | [`CotByRegions.lean`](../../src/CORALean/ContSet/Interval/Real/Operations/CotByRegions.lean), [`CotByRegionsExact.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/CotByRegionsExact.lean), [`TanUnboundedOfPole.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/TanUnboundedOfPole.lean) — both ends off the poles: the finite case is the range exactly, and `]-∞, ∞[` its hull | `underspecified` — at an end on a pole the formula is not the range |
| `Eq. 16` | `([X][Y])ᵢⱼ = Σₖ [X]ᵢₖ[Y]ₖⱼ` and `([a][X])ᵢⱼ = [a][X]ᵢⱼ`, as defined and implemented. | [`MatMul.lean`](../../src/CORALean/ContSet/Interval/Real/Operations/MatMul.lean), [`MatMulOuter.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/MatMulOuter.lean) — the product formula, enclosing every product `M N` of matrices in the factors; the paper claims no exactness, and there is none | `correct` |
| `Eq. 17` | `[X] + [X̃] = [X̲ + X̲̃, X̅ + X̃̅]`. | [`PlusExact.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/PlusExact.lean) — `Interval.plus` is generic in the ambient type, matrices included, and exact | `correct` |
| `Sec. 3` | Unary operations act elementwise, `f([X])ᵢⱼ = f([X]ᵢⱼ)`; center-radius techniques for small intervals are faster but not tight. | n/a — a convention (every `Interval` operation is coordinatewise) and a remark | `not-a-claim` |
| `Eq. 18` | The maximum relative deviation `ε` of CORA's bounds from INTLAB's over `10⁴` runs. | n/a — an experimental metric | `not-a-claim` |
| `Table 1` | The mathematical methods of the class `interval`. | n/a — a list of methods | `not-a-claim` |
| `Table 2` | The other methods of the class `interval`. | n/a — a list of methods | `not-a-claim` |
| `Table 3` | Deviation from INTLAB and computation times. | n/a — experiments | `not-a-claim` |
| `Sec. 4.1` | Two MATLAB listings and their workspace output (sums, products, quotients, powers and sines of interval matrices). | n/a — worked examples | `not-a-claim` |

## Findings

**`Eq. 14` leaves out a case.** The text announces "6 cases as for `cos`", but the cases printed
are `x̅ - x̲ ≥ π`, `z̲ > z̅` in `R_t1`, `z̲ > z̅` in `R_t2`, `z̲ ∈ R_t1` with `z̅ ∈ R_t2`, and
`z̲ ≤ z̅` in either region: the combination `z̲ ∈ R_t2`, `z̅ ∈ R_t1` (necessarily `z̲ > z̅`) matches
none. It is the range wrapping past a multiple of `π`, where the tangent is continuous and
rising, as on `[3π/4, 5π/4]`, whose range is `[tan(3π/4), tan(5π/4)] = [-1, 1]`. CORA's
`@interval/tan` lists this case in its header (`inf >= pi/2` and `sup <= pi/2` gives
`[tan(inf), tan(sup)]`), and its current code tests `tan(inf) <= tan(sup)` instead, which agrees.
Formalized with that branch.

**At an end on a pole, `Eq. 14` and `Eq. 15` are not the range.** `R_t2 = [π/2, π[` contains the
pole `π/2`, so for `[x] = [π/2, 3π/4]` the printed case `z̲ ≤ z̅` in `R_t2` answers
`[tan(π/2), tan(3π/4)]`, where `tan(π/2)` is undefined; the range on `(π/2, 3π/4]` is
`]-∞, -1]`. Likewise `cot([π, 3π/2])` reads `[cot(3π/2), cot(π)]` for the range `[0, ∞[`. With
both ends off the poles every printed case holds: the finite ones are the range exactly
(`tanByRegions_exact`, `cotByRegions_exact`), and `]-∞, ∞[` is returned exactly when a pole lies
inside, where the range is unbounded both ways, so that `]-∞, ∞[` is its interval hull — the
same reading as `1/[y]` across `0` in `Eq. 3`. The paper's tables test `tan` on
`]-π/2 + 0.1, π/2 - 0.1[`, away from the poles.
