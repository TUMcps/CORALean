module

public import CORALean.ContSet.ConPolyZono.Float.Operations.Plus
public import CORALean.ContSet.ConPolyZono.Float.Operations.PlusA
public import CORALean.ContSet.ConPolyZono.Float.Operations.PlusB
public import CORALean.ContSet.ConPolyZono.Float.Theorems.NominalPlusB
public import CORALean.ContSet.ConPolyZono.Float.Theorems.ToRealMatPlusA

@[expose] public section

/-!
# Two constraint systems side by side hold exactly when each does

The exact layer's `holds_plus_iff`, at the read-back matrices `toRealMat_plusA`
and `nominal_plusB` supply.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Two constraint systems side by side hold exactly when each holds on the
factors it came with — the exact layer's lemma, at the read-back data. -/
theorem ConPolyZono.satisfies_plus_iff (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n))
    (a : Fin (cPZ₁.p + cPZ₂.p) → ℝ) :
    (cPZ₁.plus cPZ₂).satisfies a
      ↔ cPZ₁.satisfies (fun k => a (Fin.castAdd cPZ₂.p k))
        ∧ cPZ₂.satisfies (fun k => a (Fin.natAdd cPZ₁.p k)) := by
  show Real.ConPolyZono.holds (toRealMat (ConPolyZono.plusA cPZ₁.A cPZ₂.A))
      (ConPolyZono.plusB cPZ₁.b cPZ₂.b).nominal (Real.PolyZonotope.plusE cPZ₁.EC cPZ₂.EC) a ↔ _
  rw [ConPolyZono.toRealMat_plusA, ConPolyZono.nominal_plusB]
  exact Real.ConPolyZono.holds_plus_iff _ _ _ _ _ _ a

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
