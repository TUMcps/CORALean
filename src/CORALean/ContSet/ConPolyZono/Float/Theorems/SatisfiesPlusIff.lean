import CORALean.ContSet.ConPolyZono.Float.Operations.Plus
import CORALean.ContSet.ConPolyZono.Float.Operations.PlusA
import CORALean.ContSet.ConPolyZono.Float.Operations.PlusB
import CORALean.ContSet.ConPolyZono.Float.Theorems.NominalPlusB
import CORALean.ContSet.ConPolyZono.Float.Theorems.ToRealMatPlusA

/-!
# Two constraint systems side by side hold exactly when each does

The exact layer's `holds_plus_iff`, at the read-back matrices `toRealMat_plusA`
and `nominal_plusB` supply.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Two constraint systems side by side hold exactly when each holds on the
factors it came with — the exact layer's lemma, at the read-back data. -/
theorem ConPolyZono.satisfies_plus_iff (C₁ C₂ : ConPolyZono 𝕋 n)
    (a : Fin (C₁.p + C₂.p) → ℝ) :
    (C₁.plus C₂).satisfies a
      ↔ C₁.satisfies (fun k => a (Fin.castAdd C₂.p k))
        ∧ C₂.satisfies (fun k => a (Fin.natAdd C₁.p k)) := by
  show Real.ConPolyZono.holds (toRealMat (ConPolyZono.plusA C₁.A C₂.A))
      (ConPolyZono.plusB C₁.b C₂.b).nominal (Real.PolyZonotope.plusE C₁.EC C₂.EC) a ↔ _
  rw [ConPolyZono.toRealMat_plusA, ConPolyZono.nominal_plusB]
  exact Real.ConPolyZono.holds_plus_iff _ _ _ _ _ _ a

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
