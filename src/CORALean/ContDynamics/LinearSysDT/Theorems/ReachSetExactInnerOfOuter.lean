module

public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSetExactConvex
public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSetExactIsCompact
public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffInnerOfOuter
public import Mathlib.Analysis.InnerProductSpace.Basic

@[expose] public section

/-!
# The bridge, discharged: an outer approximation of `reachSetExact` inverts

`minkowskiDiff_inner_of_outer` turns an outer approximation `Ŷ ⊆ Y + E` into an
inner one, `minkowskiDiff Ŷ E ⊆ Y`, once `Y` is convex and closed. At `Y :=
reachSetExact sys R₀ U k` that hypothesis is exactly `reachSetExact_convex` and
`reachSetExact_isCompact` (for the closedness), so a caller supplies only what is
true of `R₀`, `U` and the error set `E` — nothing about `reachSetExact` itself is
left to discharge.

## Inputs
* `sys` – system
* `R₀` – initial set
* `U` – input set
* `k` – step
* `Ŷ` – outer approximation
* `E` – error set

## Hypotheses
* `hR₀conv` – initial set convex
* `hR₀comp` – initial set compact
* `hUconv` – input set convex
* `hUcomp` – input set compact
* `hE` – `E` nonempty
* `hEb` – `E` bounded
* `hOuter` – `Ŷ` lies in the exact set plus `E`

## Conclusion
* the Minkowski difference of `Ŷ` and `E` lies in the exact set
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- An outer approximation `Ŷ` of `reachSetExact sys R₀ U k`, with error bounded by a
nonempty bounded `E`, becomes an inner approximation once `E` is taken back off
— provided `R₀` and `U` are convex and compact, which is all this asks of them. -/
theorem LinearSysDT.reachSetExact_inner_of_outer (sys : LinearSysDT 𝕋 n) {R₀ U : S n}
    (hR₀conv : Convex ℝ (construct R₀)) (hR₀comp : IsCompact (construct R₀))
    (hUconv : Convex ℝ (construct U)) (hUcomp : IsCompact (construct U)) (k : ℕ)
    {Ŷ E : Set (Vec ℝ n)} (hE : E.Nonempty) (hEb : Bornology.IsBounded E)
    (hOuter : Ŷ ⊆ sys.reachSetExact R₀ U k + E) : -- --- CONCL ---
    minkowskiDiff Ŷ E ⊆ sys.reachSetExact R₀ U k :=
  minkowskiDiff_inner_of_outer hE hEb (sys.reachSetExact_convex hR₀conv hUconv k)
    (sys.reachSetExact_isCompact hR₀comp hUcomp k).isClosed hOuter

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
