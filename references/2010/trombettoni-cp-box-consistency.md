# A Box-Consistency Contractor Based on Extremal Functions

```bibtex
@inproceedings{trombettoni2010box,
  author = {Trombettoni, G. and Papegay, Y. and Chabert, G. and Pourtallier, O.},
  title = {A Box-Consistency Contractor Based on Extremal Functions},
  booktitle = {Principles and Practice of Constraint Programming – CP 2010},
  year = {2010}
}
```

**Source:** https://www.lirmm.fr/~trombetton/publis/63080491.pdf (the Springer LNCS pages 491-498 as published, 8 pages, read in full; text extracted with `pypdf`, so over- and underlines are lost and which of `g̲`, `g̅` a formula means is read from the cases it states). CORA's `contract`, `contractPoly` and `contractPolyBoxRevise` cite it as "G. Trombettoni et al., 2010"; the author list is the paper's own, Trombettoni, Papegay, Chabert and Pourtallier.  
**Inventory:** confirmed (the numbered items are Definitions 1-2, Figure 1 and Table 1; Sec. 3 states the extremal functions, an example, a remark, the three cases of the contraction and the four cases of `PolyBoxRevise` in prose, which are rows of their own, named by section)

The contractor behind CORA's `contractPolyBoxRevise` (`contract(f, dom, 'polynomial')`). A
constraint `f(x, y) = Σᵢ fᵢ(y) hᵢ(x) = 0` is narrowed in one variable `x` by two real functions
enclosing it, the extremal functions `g̲ ≤ f ≤ g̅`, read off the interval coefficients
`[cᵢ] = [fᵢ]_N([Y])` at the bound the sign of `hᵢ(x)` selects; the new left bound of `[x]` is the
smallest root of whichever extremal function excludes `x̲`. CORALean formalizes the extremal
functions, that they are the optimal ones (`IsLeast`/`IsGreatest` over the coefficient box),
the three cases of the bound update with the root search as a parameter, and the polynomial
case `hᵢ(x) = xⁱ` assembled into a contractor in the sense of `IsContractor`. The box it returns
lies in the box it was given and keeps every solution, so contraction removes none. What is
not modelled is the floating-point side — box consistency is defined by one-u.l.p. slices — and
Cardano's formulas, which are one root search among others.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Sec. 1` | Interval methods approximate all real solutions; contraction algorithms filter the variable domains without loss of solutions; `BoxNarrow` works with the interval function `f[Y]`, `PolyBox` with two non-interval functions. | n/a — motivation; the no-loss property is what `Sec. 3 (PolyBoxRevise)` proves | `not-a-claim` |
| `Def. 1` | Intervals `[v] = [a, b]` with floating-point bounds, the size `v̅ - v̲`, boxes `[V] = [v₁] × … × [vₙ]`; interval arithmetic, e.g. `[v₁] + [v₂] = [v̲₁ + v̲₂, v̅₁ + v̅₂]`; an extension `[f]` is conservative if `f(V) = [f](V)` and `[f]([V]) ⊇ {f(V), V ∈ [V]}`. | n/a — notation and Moore's interval arithmetic [10]; the sum is CORALean's `Interval.plus`, exact, and a conservative extension is what `Sec. 3 (PolyBoxRevise)` assumes of the coefficients | `restated` |
| `Sec. 2 (natural extension)` | The natural extension of `f(x₁, x₂) = x₁² - 2x₁x₂ + x₂²` on `[x₁] = [x₂] = [0, 1]` is `[-2, 2]`; rewritten as `(x₁ - x₂)²` it is `([x₁] - [x₂])² = [0, 1] = {f(x₁, x₂)} ⊂ [-2, 2]`: the dependency problem. | [`NaturalExtensionDependency.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/NaturalExtensionDependency.lean) — both evaluated with CORALean's `power`, `times`, `smul`, `minus`, `plus`, and the range on the box | `correct` |
| `Sec. 2 (hull consistency)` | Finding the optimal interval image of a polynomial is NP-hard [8]; `HC4-Revise` achieves hull consistency of a constraint with no multiple occurrence [2]. `BoxNarrow` is stronger [4] and achieves it with one multiply occurring variable; hull consistency is not tractable. | n/a — restated from [2], [4] and [8] | `restated` |
| `Sec. 2 (NCSP)` | An NCSP `(V, C, [V])`, its solutions, and the Branch & Contract search that bisects and contracts until the boxes are smaller than `ω`. | n/a — a description of the solver scheme | `not-a-claim` |
| `Def. 2` | `(c, x)` is box-consistent on `[x]` if `0 ∈ [f[Y]]_N([x̲, x̲⁺])` and `0 ∈ [f[Y]]_N([x̅⁻, x̅])`, the slices one u.l.p. wide; `BoxNarrow` returns the smallest and largest `ε`-solutions. | n/a — box consistency is defined by one-u.l.p. slices at floating-point bounds; CORALean's contractors are stated over ℝ, and its float layer rounds outward rather than slicing by u.l.p. | `not-covered` |
| `Fig. 1` | The steps of `BoxNarrow` (`LeftNarrow`, `RightNarrow`) on `f[Y]`. | n/a — an illustration of `BoxNarrow`, which is [2]'s | `not-a-claim` |
| `Sec. 3 (extremal functions)` | With `h̲(x) = min_{yᵢ ∈ [yᵢ]} f(x, y)` and `h̅(x)` the maximum, `0 ∈ [h̲(x), h̅(x)]` is a necessary and sufficient condition for `x ∈ [x]` to satisfy `c`. | [`ExistsZeroIffExtrema.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/ExistsZeroIffExtrema.lean), [`ExistsZeroIffExtrema.lean`](../../src/CORALean/ContSet/Interval/Real/Counterexamples/ExistsZeroIffExtrema.lean) — for `f(x, ·)` continuous on the box (any preconnected set), with a counterexample without continuity **Counterexample:** `Interval.exists_zero_iff_extrema_counterexample` **Counterexample:** `Interval.exists_zero_iff_extrema_counterexample` | `fixed` — sufficiency is false for `f(x, ·)` not continuous, needs `f(x, ·)` continuous, see the findings |
| `Sec. 3 (necessary condition)` | For any `g̲ ≤ h̲ ≤ f ≤ h̅ ≤ g̅` on `[x] × [Y]`, the test `0 ∈ [g̲(x), g̅(x)]` is only a necessary condition. | [`ZeroMemExtremal.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/ZeroMemExtremal.lean) — a solution passes the test, for the extremal functions below; "only" is `Sec. 3 (extremal functions)`'s counterpart, the extremal functions being looser than `h̲`, `h̅` | `correct` |
| `Sec. 3 (extremal bounds)` | For `f = Σ_{i=0}^d fᵢ(y) hᵢ(x)`, `hᵢ` of known sign, `g[Y](x) = Σ_{i=0}^d [cᵢ] hᵢ(x)`, the functions `g̲[Y](x) = Σ_{i=1}^d cᵢ⁻(x) hᵢ(x)` and `g̅[Y](x) = Σ_{i=1}^d cᵢ⁺(x) hᵢ(x)`, `cᵢ⁻ = c̲ᵢ`, `cᵢ⁺ = c̅ᵢ` where `hᵢ(x) ≥ 0` and swapped where `hᵢ(x) ≤ 0`, are minimal and maximal extremal functions. | [`ExtremalLo.lean`](../../src/CORALean/ContSet/Interval/Real/Operations/ExtremalLo.lean), [`ExtremalHi.lean`](../../src/CORALean/ContSet/Interval/Real/Operations/ExtremalHi.lean), [`ExtremalLoIsLeast.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/ExtremalLoIsLeast.lean), [`ExtremalHiIsGreatest.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/ExtremalHiIsGreatest.lean) — summed from `i = 0`; `g̲(x) ≤ Σᵢ cᵢ hᵢ(x) ≤ g̅(x)` for every `cᵢ ∈ [cᵢ]`, so `g̲ ≤ f ≤ g̅` wherever `[cᵢ] ∋ fᵢ(y)` | `underspecified` — the extremal sums start at `i = 1`, dropping the constant term `g[Y]` and the example carry |
| `Sec. 3 (example)` | `f = (y₁ + y₂)x² + (2y₁y₂)x + sin(y₂)` on `[y₁] = [0.5, 1]`, `[y₂] = [1, 2]`: `g[Y](x) = [1.5, 3]x² + [1, 4]x + [0.84147, 1]`, `g̲ = 1.5x² + x + 0.84147` (`x ≥ 0`), `1.5x² + 4x + 0.84147` (`x ≤ 0`), `g̅ = 3x² + 4x + 1` (`x ≥ 0`), `3x² + x + 1` (`x ≤ 0`). | [`ExtremalExample.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/ExtremalExample.lean) — the three coefficient ranges, `sin([1, 2]) = [sin 1, 1]` with `0.84147 < sin 1 < 0.84148`, and the four branches | `correct` |
| `Remark (optimal)` | `g̲[Y]` and `g̅[Y]` are optimal extremal functions of `g[Y]`. | [`ExtremalLoIsLeast.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/ExtremalLoIsLeast.lean), [`ExtremalHiIsGreatest.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/ExtremalHiIsGreatest.lean) — at every `x` the least and greatest of `Σᵢ cᵢ hᵢ(x)` over the coefficient box, and taken | `correct` |
| `Remark (comparison)` | `f[Y]` and `g[Y]` differ, the multiple occurrences overestimating differently; the box consistencies of `f[Y]` and `g[Y]` are not comparable, so the contractor calls `HC4-Revise` on `f` first. | n/a — box consistency is defined by one-u.l.p. slices, as in `Def. 2` | `not-covered` |
| `Sec. 3 (three cases)` | The new left bound `l̲`: 1. `g̲(x̲) ≤ 0 ≤ g̅(x̲)`: `l = x̲`; 2. `g̲(x̲) > 0`: `g̲` is selected; 3. `g̅(x̲) < 0`: `g̅` is selected; `l` is the smallest root of the selected function in `[x]`, by `BoxNarrow` on it; the right bound symmetrically. | [`PolyBoxReviseLeft.lean`](../../src/CORALean/ContSet/Interval/Real/Operations/PolyBoxReviseLeft.lean), [`PolyBoxReviseRight.lean`](../../src/CORALean/ContSet/Interval/Real/Operations/PolyBoxReviseRight.lean), [`RootBound.lean`](../../src/CORALean/ContSet/Interval/Real/Definitions/RootBound.lean), [`PolyBoxReviseLeftLe.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/PolyBoxReviseLeftLe.lean), [`PolyBoxReviseRightGe.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/PolyBoxReviseRightGe.lean) — every `x` passing `g̲(x) ≤ 0 ≤ g̅(x)` lies between the new bounds, for continuous extremal functions and any root search leaving no zero on the far side of its answer (the smallest root does) | `correct` |
| `Sec. 3 (PolyBoxRevise)` | The polynomial case `hᵢ(x) = xⁱ`, roots in closed form below degree 4 (Cardano), `BoxNarrow` otherwise; `PolyBoxRevise` calls `HC4-Revise` when `f` has one occurrence of `x` or is not polynomial (or `BoxNarrow`), when `g[Y]` has one occurrence of `x`, and the extremal contraction otherwise. | [`PolyBoxRevise.lean`](../../src/CORALean/ContSet/Interval/Real/Operations/PolyBoxRevise.lean), [`PolyBoxReviseIsContractor.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/PolyBoxReviseIsContractor.lean) — the extremal contraction of a polynomial constraint on one coordinate is a contractor (`IsContractor`): result inside the box, every solution kept, for coefficients enclosed by their extension and root searches as in `Sec. 3 (three cases)`; the result is intersected with `[x]`, as CORA does. The search is a parameter, so Cardano's formulas are one admissible instance and are not themselves formalized; the `HC4-Revise` and `BoxNarrow` branches are [2]'s | `correct` |
| `Sec. 3 (remarks)` | Caprasse's `-2x + 2txy - z + y²z = 0` is rewritten `(-2 + 2ty)x + (-1 + y²)z = 0`, where `x`, `z` occur once; 6body's `5(b₁ - d₁) + 3(b₂ - d₂)(b₁ + d₁ - 2f₁) = 0` becomes `b₁(5 + 3(b₂ - d₂)) + (-5 + 3b₂ - 3d₂)d₁ + 6(-b₂ + d₂)f₁ = 0`, a counterproductive rewriting. | [`PolyBoxRewriteRemarks.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/PolyBoxRewriteRemarks.lean) — both rewritings are identities; the CPU-time effects are measurements, and the 6body sentence's "`a₂`" names no variable of the equation | `correct` |
| `Sec. 3 (Numerica)` | Numerica uses extremal functions on an entirely expanded copy of the system; `PolyBox` keeps one system with a revise procedure per pair, which overestimates less, and adds the analytic solving of low degrees. | n/a — a comparison of two solvers' designs | `not-a-claim` |
| `Table 1` | CPU times and search-tree sizes of `HC4`, `BC4`, `PolyBox--` and `PolyBox` on twelve polynomial systems. | n/a — experiments | `not-a-claim` |
| `Sec. 4` | The experimental setup (Ibex, round-robin bisection, interval Newton) and its conclusions. | n/a — experiments | `not-a-claim` |

## Findings

**`Sec. 3 (extremal functions)` needs continuity.** The paper calls `0 ∈ [h̲(x), h̅(x)]` "a
necessary and sufficient condition" for `x` to satisfy `f(x, y) = 0` with some `y ∈ [Y]`.
Necessity holds for any `f`. Sufficiency is the intermediate value theorem on the box and needs
`f(x, ·)` continuous there: `f(x, y) = -1` for `y ≤ 0` and `1` for `y > 0` on `[Y] = [-1, 1]` has
minimum `-1` and maximum `1` and no zero
([`ExistsZeroIffExtrema.lean`](../../src/CORALean/ContSet/Interval/Real/Counterexamples/ExistsZeroIffExtrema.lean)).
The paper's constraints are polynomials and elementary functions, so its setting is
continuous; the formalization states it.

**The extremal sums start at `i = 1`.** `g[Y](x) = Σ_{i=0}^d [fᵢ]_N([Y]) hᵢ(x)` and the example's
constant term `[0.84147, 1]` (`h₀ = 1`) put the index at `0`, while `g̲[Y]` and `g̅[Y]` are printed
`Σ_{i=1}^d`. Read literally they drop the constant term, and the example's `g̲` and `g̅` would lose
their `+ 0.84147` and `+ 1`. `Interval.extremalLo` and `extremalHi` sum every index, which is
what the example computes.
