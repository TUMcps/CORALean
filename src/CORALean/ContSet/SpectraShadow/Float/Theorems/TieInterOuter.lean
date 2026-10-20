module

public import CORALean.ContSet.SpectraShadow.Float.Operations.TieInter
public import CORALean.ContSet.SpectraShadow.Float.Theorems.LmiBlockDiagDiagonal
public import CORALean.ContSet.SpectraShadow.Float.Theorems.MemNominalSet
public import CORALean.ContSet.SpectraShadow.Float.Theorems.ToRealMatConstZero
public import CORALean.ContSet.Interval.Float.Theorems.OriginExact

@[expose] public section

/-!
# `SpectraShadow.tieInter` contains the intersection of the nominal shadows

A common point `x = c₁ + G₁ β₁ = c₂ + G₂ β₂` is the tied shadow's point at the variables
`(β₁, β₂, x)`: both inequalities hold, and every tie entry is `0`. The box is the origin.

## Inputs
* `S₁` – spectrahedral shadow
* `S₂` – spectrahedral shadow

## Hypotheses
* none

## Conclusion
* `SpectraShadow.tieInter` contains the intersection of the nominal shadows
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.tieInter_outer (S₁ S₂ : SpectraShadow 𝕋 (Vec 𝕋 n)) :
    nominalSet S₁ ∩ nominalSet S₂ ⊆ (S₁.tieInter S₂).construct := by -- --- PROOF ---
  rintro x ⟨h₁, h₂⟩
  obtain ⟨β₁, hP₁, hx₁⟩ := SpectraShadow.mem_nominalSet_iff.mp h₁
  obtain ⟨β₂, hP₂, hx₂⟩ := SpectraShadow.mem_nominalSet_iff.mp h₂
  have hd : ∀ {b : ℕ} (w : Vec 𝕋 b),
      toRealMat (diagonalBlock w) = Matrix.diagonal (toRealVec w) := by
    intro b w
    ext i l
    simp [toRealMat, toReal_diagonalBlock]
  have hunit : ∀ i r : Fin n, toReal (if r = i then (one : 𝕋) else zero) = if r = i then 1 else 0 :=
    fun i r => by split_ifs <;> simp [toReal_one, toReal_zero]
  -- the box is the origin, so the nominal point is the point
  refine ⟨x, ?_, 0, ?_, add_zero x⟩
  swap
  · show (0 : Vec ℝ n) ∈ (Interval.origin n : Interval (Vec 𝕋 n)).construct
    rw [Interval.origin_exact]
    rfl
  refine SpectraShadow.mem_nominalSet_iff.mpr ⟨Fin.append (Fin.append β₁ β₂) x, ?_, fun r => ?_⟩
  · -- the inequality is the two old ones beside the ties' diagonal
    show (toRealMat (blockDiag zero (blockDiag zero S₁.A₀ S₂.A₀) _)
      + ∑ l : Fin ((S₁.m + S₂.m) + n),
        (Fin.append (Fin.append β₁ β₂) x : Fin ((S₁.m + S₂.m) + n) → ℝ) l
          • toRealMat (blockDiag zero _ (diagonalBlock _))).PosSemidef
    simp only [SpectraShadow.toRealMat_blockDiag, hd]
    rw [SpectraShadow.lmi_blockDiag_diagonal]
    refine (posSemidef_blockDiag_iff _ _).mpr ⟨?_, Matrix.posSemidef_diagonal_iff.mpr fun r => ?_⟩
    · -- the old variables carry the old matrices, block by block
      rw [Fin.sum_univ_add, Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, SpectraShadow.toRealMat_blockDiag,
        SpectraShadow.toRealMat_const_zero, smul_zero, Finset.sum_const_zero, add_zero]
      simp only [← blockDiag_smul, ← blockDiag_sum, ← blockDiag_add, smul_zero,
        Finset.sum_const_zero, add_zero, zero_add]
      exact (posSemidef_blockDiag_iff _ _).mpr ⟨hP₁, hP₂⟩
    · -- every tie entry is zero at the common point
      rw [Fin.sum_univ_add, Fin.sum_univ_add]
      refine Fin.addCases (fun r₁ => ?_) (fun r₁ => ?_) r <;>
        refine Fin.addCases (fun r' => ?_) (fun r' => ?_) r₁ <;>
        have e₁ := hx₁ r' <;> have e₂ := hx₂ r' <;>
        have s₁ : ∑ j, β₁ j * toReal (S₁.G j r') = ∑ j, toReal (S₁.G j r') * β₁ j :=
          Finset.sum_congr rfl fun _ _ => mul_comm _ _ <;>
        have s₂ : ∑ j, β₂ j * toReal (S₂.G j r') = ∑ j, toReal (S₂.G j r') * β₂ j :=
          Finset.sum_congr rfl fun _ _ => mul_comm _ _ <;>
        simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, toRealVec,
          Fin.append_left, Fin.append_right] <;>
        simp [toReal_zero, toReal_neg', hunit, Finset.sum_neg_distrib] <;>
        linarith
  · -- the point is the tied variable
    show x r = toReal (zero : 𝕋) + ∑ l : Fin ((S₁.m + S₂.m) + n),
      toReal (Fin.append (fun (_ : Fin (S₁.m + S₂.m)) (_ : Fin n) => (zero : 𝕋))
        (fun (i r' : Fin n) => if r' = i then (one : 𝕋) else zero) l r)
        * (Fin.append (Fin.append β₁ β₂) x : Fin ((S₁.m + S₂.m) + n) → ℝ) l
    rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right, hunit, toReal_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
