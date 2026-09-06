import CORALean.ContSet.PolyZonotope.Real.Operations.FactorExtend

/-!
# `factorExtend` stays within `[-1, 1]`

Split out of `Compact.lean` (issue #62): reused unchanged by
`ConPolyZono.abs_factorExtend_le_one`, outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.abs_factorExtend_le_one {p h : ℕ} (E : Fin p → Fin h → ℕ)
    {a : Fin (PolyZonotope.usedFactors E).card → ℝ} (ha : ∀ k, |a k| ≤ 1) (k : Fin p) :
    |PolyZonotope.factorExtend E a k| ≤ 1 := by -- --- PROOF ---
  rw [PolyZonotope.factorExtend]
  split
  · exact ha _
  · rw [abs_zero]; exact zero_le_one

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
