module

public import CORALean.ContSet.ConPolyZono.Float.Operations.LinComb
public import CORALean.ContSet.ConPolyZono.Float.Theorems.NominalPlusB
public import CORALean.ContSet.ConPolyZono.Float.Theorems.ToRealMatPlusA
public import CORALean.ContSet.ConPolyZono.Real.Operations.HoldsPadEIff
public import CORALean.ContSet.ConPolyZono.Real.Operations.HoldsPlusIff

@[expose] public section

/-!
# `ConPolyZono.linComb`'s constraint reads each side's own factors

The exact layer's `satisfies_linComb_iff`, at the read-back data:
`holds_padE_iff` drops the fresh segment factor, which no constraint monomial
reads, and `holds_plus_iff` splits what is left at `toRealMat_plusA` and
`nominal_plusB`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.satisfies_linComb_iff (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n))
    (a : Fin (cPZ₁.p + cPZ₂.p + 1) → ℝ) : -- --- STMT ---
    (cPZ₁.linComb cPZ₂).satisfies a
      ↔ cPZ₁.satisfies (fun k => a (Fin.castAdd 1 (Fin.castAdd cPZ₂.p k)))
        ∧ cPZ₂.satisfies (fun k => a (Fin.castAdd 1 (Fin.natAdd cPZ₁.p k))) := by -- --- PROOF ---
  show Real.ConPolyZono.holds (toRealMat (ConPolyZono.plusA cPZ₁.A cPZ₂.A))
      (ConPolyZono.plusB cPZ₁.b cPZ₂.b).nominal
      (Real.ConPolyZono.padE (Real.PolyZonotope.plusE cPZ₁.R cPZ₂.R) 1) a ↔ _
  rw [ConPolyZono.toRealMat_plusA, ConPolyZono.nominal_plusB]
  exact (Real.ConPolyZono.holds_padE_iff _ _ _ 1 a).trans
    (Real.ConPolyZono.holds_plus_iff _ _ _ _ _ _ (fun k => a (Fin.castAdd 1 k)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
