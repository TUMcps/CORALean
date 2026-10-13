import CORALean.ContSet.PolyZonotope.Real.Operations.ReplaceId
import CORALean.ContSet.PolyZonotope.Real.Operations.Point
import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialReplaceId

/-!
# `PolyZonotope.replaceId` evaluates the original at the renamed factors

The monomial of the renamed set at `a'` is the original monomial at `a' ∘ f`: the product of
`a'ₖ'` to the summed exponents regroups into the product over the factors, each at its new name.
So the renamed set's dependent points are the original's at the factor vectors that are constant
on the fibres of `f`; `replaceId_subset` and, for an injective `f` (a plain renaming),
`replaceId_exact` follow. Identifying two factors adds a dependency and shrinks the set.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.replaceId_point (pZ : PolyZonotope α) {p' : ℕ} (f : Fin pZ.p → Fin p')
    (a' : Fin p' → ℝ) : (pZ.replaceId f).point a' = pZ.point (fun k => a' (f k)) := by
  unfold PolyZonotope.point
  simp only [PolyZonotope.replaceId]
  exact congrArg (fun s => pZ.c + s) (Finset.sum_congr rfl fun i _ => by
    rw [PolyZonotope.monomial_replaceId])

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
