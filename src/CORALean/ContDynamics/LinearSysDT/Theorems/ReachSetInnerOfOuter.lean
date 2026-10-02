import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSetConvex
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSetIsCompact
import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffInnerOfOuter
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The bridge, discharged: an outer approximation of `reachSet` inverts

`minkowskiDiff_inner_of_outer` turns an outer approximation `Ŷ ⊆ Y + E` into an
inner one, `minkowskiDiff Ŷ E ⊆ Y`, once `Y` is convex and closed. At `Y :=
reachSet sys R₀ U k` that hypothesis is exactly `reachSet_convex` and
`reachSet_isCompact` (for the closedness), so a caller supplies only what is
true of `R₀`, `U` and the error set `E` — nothing about `reachSet` itself is
left to discharge.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- An outer approximation `Ŷ` of `reachSet sys R₀ U k`, with error bounded by a
nonempty bounded `E`, becomes an inner approximation once `E` is taken back off
— provided `R₀` and `U` are convex and compact, which is all this asks of them. -/
theorem LinearSysDT.reachSet_inner_of_outer (sys : LinearSysDT 𝕋 n) {R₀ U : S n}
    (hR₀conv : Convex ℝ (construct R₀)) (hR₀comp : IsCompact (construct R₀))
    (hUconv : Convex ℝ (construct U)) (hUcomp : IsCompact (construct U)) (k : ℕ)
    {Ŷ E : Set (Vec ℝ n)} (hE : E.Nonempty) (hEb : Bornology.IsBounded E)
    (hOuter : Ŷ ⊆ sys.reachSet R₀ U k + E) :
    minkowskiDiff Ŷ E ⊆ sys.reachSet R₀ U k :=
  minkowskiDiff_inner_of_outer hE hEb (sys.reachSet_convex hR₀conv hUconv k)
    (sys.reachSet_isCompact hR₀comp hUcomp k).isClosed hOuter

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
