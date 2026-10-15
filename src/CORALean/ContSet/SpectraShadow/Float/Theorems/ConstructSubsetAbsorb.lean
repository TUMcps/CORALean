module

public import CORALean.ContSet.SpectraShadow.Float.Operations.Absorb
public import CORALean.ContSet.SpectraShadow.Float.Theorems.LmiBlockDiagDiagonal
public import CORALean.ContSet.SpectraShadow.Float.Theorems.MemNominalSet
public import CORALean.ContSet.SpectraShadow.Float.Theorems.ToRealMatConstZero

@[expose] public section

/-!
# `SpectraShadow.absorb` holds the whole set in its nominal shadow

A point `c + Gβ + e`, `e` in the box, is the absorbed shadow's nominal point at the variables
`(β, e)`: the old inequality holds at `β`, and the box constraints at `e` are the box's own
bounds. So the set lies in the nominal part alone, and (the box being the origin) in the
absorbed set.
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

theorem SpectraShadow.construct_subset_absorb (S : SpectraShadow 𝕋 (Vec 𝕋 n)) :
    S.construct ⊆ nominalSet S.absorb := by -- --- PROOF ---
  rintro _ ⟨y, hy, e, he, rfl⟩
  obtain ⟨β, hP, hyβ⟩ := SpectraShadow.mem_nominalSet_iff.mp hy
  have hd : ∀ {b : ℕ} (w : Vec 𝕋 b),
      toRealMat (diagonalBlock w) = Matrix.diagonal (toRealVec w) := by
    intro b w
    ext i l
    simp [toRealMat, toReal_diagonalBlock]
  have hunit : ∀ i r : Fin n, toReal (if r = i then (one : 𝕋) else zero) = if r = i then 1 else 0 :=
    fun i r => by split_ifs <;> simp [toReal_one, toReal_zero]
  refine SpectraShadow.mem_nominalSet_iff.mpr ⟨Fin.append β e, ?_, fun r => ?_⟩
  · -- the inequality is the old one beside the box constraints' diagonal
    show (toRealMat (blockDiag zero S.A₀ _) + ∑ l : Fin (S.m + n),
      (Fin.append β e : Fin (S.m + n) → ℝ) l • toRealMat (blockDiag zero _ (diagonalBlock _))
      ).PosSemidef
    simp only [SpectraShadow.toRealMat_blockDiag, hd]
    rw [SpectraShadow.lmi_blockDiag_diagonal]
    refine (posSemidef_blockDiag_iff _ _).mpr ⟨?_, Matrix.posSemidef_diagonal_iff.mpr fun r => ?_⟩
    · -- the old variables carry the old matrices, the new ones zero
      rw [Fin.sum_univ_add]
      simpa [Fin.append_left, Fin.append_right, SpectraShadow.toRealMat_const_zero] using hP
    · -- each box constraint is the box's bound at `e`
      rw [Fin.sum_univ_add]
      refine Fin.addCases (fun r' => ?_) (fun r' => ?_) r <;>
        have hb : toReal (S.I_error.inf r') ≤ e r' ∧ e r' ≤ toReal (S.I_error.sup r') := he r' <;>
        simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, toRealVec,
          Fin.append_left, Fin.append_right] <;>
        simp [toReal_zero, toReal_neg', hunit] <;> linarith [hb.1, hb.2]
  · -- the point is the old one plus the error
    show y r + e r = toReal (S.c r) + ∑ l : Fin (S.m + n),
      toReal (Fin.append S.G (fun (i r' : Fin n) => if r' = i then (one : 𝕋) else zero) l r)
        * (Fin.append β e : Fin (S.m + n) → ℝ) l
    rw [Fin.sum_univ_add, hyβ r]
    simp [Fin.append_left, Fin.append_right, hunit, add_assoc]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
