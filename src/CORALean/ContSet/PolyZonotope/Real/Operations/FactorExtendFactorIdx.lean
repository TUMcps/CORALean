import CORALean.ContSet.PolyZonotope.Real.Operations.FactorExtend
import CORALean.ContSet.PolyZonotope.Real.Operations.FactorIdx

/-!
# On a kept factor, extension is the identity

Split out of `Compact.lean` (issue #62): used again by
`Theorems/CompactFactorsExact.lean`, and by `ConPolyZono`'s own
`MonomialFactorExtendLeft`/`Right.lean`, both outside this file.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.factorExtend_factorIdx {p h : ℕ} (E : Fin p → Fin h → ℕ)
    (a : Fin (PolyZonotope.usedFactors E).card → ℝ)
    (k : Fin (PolyZonotope.usedFactors E).card) :
    PolyZonotope.factorExtend E a (PolyZonotope.factorIdx E k) = a k := by -- --- PROOF ---
  have hmem : PolyZonotope.factorIdx E k ∈ PolyZonotope.usedFactors E :=
    ((PolyZonotope.usedFactors E).orderIsoOfFin rfl k).2
  rw [PolyZonotope.factorExtend, dif_pos hmem]
  congr 1
  rw [show (⟨PolyZonotope.factorIdx E k, hmem⟩ : {x // x ∈ PolyZonotope.usedFactors E})
      = (PolyZonotope.usedFactors E).orderIsoOfFin rfl k from Subtype.ext rfl]
  exact ((PolyZonotope.usedFactors E).orderIsoOfFin rfl).symm_apply_apply k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
