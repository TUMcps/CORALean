module

public import CORALean.ContSet.SpectraShadow.Float.Operations.GenerateESumRep
public import CORALean.ContSet.SpectraShadow.Float.Theorems.ToRealMatBlockDiag
public import CORALean.ContSet.SpectraShadow.Float.Theorems.ToRealMatConstZero
public import CORALean.ContSet.SpectraShadow.Real.Theorems.GenerateESumRepExact

@[expose] public section

/-!
# The float `generateESumRep` denotes the nominal shadow exactly

Exact, nothing rounds: the stored matrices of the float representation read, entry by entry, as
the matrices the exact layer's `generateESumRep` builds from the nominal shadow, so the set of the
representation is the set of the stored shadow's nominal part. The shadow's error box is not
carried by the representation, so the statement is about `nominalSet`, not `construct`.

## Inputs
* `S` – spectrahedral shadow

## Hypotheses
* none

## Conclusion
* the float `generateESumRep` denotes the nominal shadow exactly
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic CORALean

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.generateESumRep_exact (S : SpectraShadow 𝕋 (Vec 𝕋 n)) : -- --- CONCL ---
    S.generateESumRep.construct = InflatedContSet.nominalSet S := by -- --- PROOF ---
  have hd : ∀ v : Vec 𝕋 n, toRealMat (diagonalBlock v) = Matrix.diagonal (toRealVec v) :=
    fun v => by ext i l; exact toReal_diagonalBlock v i l
  have hsingle : ∀ i : Fin n, toRealVec (fun r => if r = i then (one : 𝕋) else zero)
      = (Pi.single i 1 : Vec ℝ n) := fun i => by
    funext r
    by_cases h : r = i
    · subst h; simp [toRealVec, toReal_one]
    · simp [toRealVec, h, toReal_zero]
  -- the stored matrices read as the exact layer's, so the exact theorem applies
  have hrep : (⟨S.generateESumRep.k, S.generateESumRep.q, toRealMat S.generateESumRep.B₀,
      fun i => toRealMat (S.generateESumRep.B i), fun j => toRealMat (S.generateESumRep.C j)⟩ :
      CORALean.Real.SpectraShadow.ESumRep n)
      = CORALean.Real.SpectraShadow.generateESumRep (InflatedContSet.nominal S) := by
    simp only [SpectraShadow.generateESumRep, CORALean.Real.SpectraShadow.generateESumRep,
      SpectraShadow.toRealMat_blockDiag, SpectraShadow.toRealMat_const_zero, hd, toRealVec_neg,
      hsingle]
    rfl
  unfold SpectraShadow.ESumRep.construct
  rw [hrep]
  exact CORALean.Real.SpectraShadow.generateESumRep_exact _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
