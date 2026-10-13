module

public import CORALean.ContSet.ConPolyZono.Float.Operations.Union
public import CORALean.ContSet.ConPolyZono.Float.Theorems.UnionUpperHolds
public import CORALean.ContSet.ConPolyZono.Float.Theorems.UnionLowerHolds
public import CORALean.ContSet.ConPolyZono.Real.Operations.HoldsSharedIff
public import CORALean.ContSet.ConPolyZono.Real.Operations.Union

@[expose] public section

/-!
# The stored union's constraints hold wherever the exact union's do

At a factor vector in the cube, the exact union of the two read-back operands satisfies its
constraints only if the stored one does: its selector rows and its two operand blocks each hold
(`holds_unionUpper_of_real`, `holds_unionLower_of_real`), the stored system being the exact one
with its bounds widened and the selector row scaled.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.union_satisfies_of_real (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n))
    (a : Fin (cPZ₁.p + cPZ₂.p + 2) → ℝ) (ha : ∀ k, |a k| ≤ 1)
    (h : (Real.ConPolyZono.union (nominal cPZ₁) (nominal cPZ₂)).satisfies a) :
    (cPZ₁.union cPZ₂).satisfies a := by -- --- PROOF ---
  unfold ConPolyZono.satisfies ConPolyZono.union
  rw [ConPolyZono.toRealMat_plusA, ConPolyZono.nominal_plusB,
    Real.ConPolyZono.holds_shared_iff]
  obtain ⟨hup, hlow⟩ := (Real.ConPolyZono.holds_shared_iff _ _ _ _ _ _ a).mp h
  exact ⟨ConPolyZono.holds_unionUpper_of_real _ _ a ha hup,
    ConPolyZono.holds_unionLower_of_real _ _ _ _ _ _ a hlow⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
