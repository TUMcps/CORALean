module

public import CORALean.ContSet.SpectraShadow.Float.Operations.DualBound
public import CORALean.ContSet.SpectraShadow.Float.Operations.DualCertified
public import CORALean.ContSet.SpectraShadow.Float.Theorems.MemNominalSet
public import CORALean.ContSet.SpectraShadow.Float.Theorems.PosSemidefOfDiagDominant
public import CORALean.ContSet.SpectraShadow.Real.Theorems.TraceMulNonneg

@[expose] public section

/-!
# A certified `Y` bounds the shadow along `a`

Weak duality, as over ℝ (`CORALean.Real.SpectraShadow.supportBound`): `Y ⪰ 0` (diagonally
dominant) and the inequality's matrix at `β` give `tr(M(β) Y) ≥ 0`, which with the exact
equalities is `aᵀ G β ≤ tr(A₀ Y)`. The rounded-up sums bound the nominal part, and each
coordinate of the error lies between its corners, where `aᵣ eᵣ` is largest.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic ToRat InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [ToRat 𝕋] in
/-- A product with a factor between two corners is at most the larger corner product. -/
theorem SpectraShadow.aux_mul_le_corner (a lo hi : 𝕋) {e : ℝ} (he₁ : toReal lo ≤ e)
    (he₂ : e ≤ toReal hi) :
    toReal a * e ≤ toReal (maximum (mulUp a lo) (mulUp a hi)) := by -- --- PROOF ---
  rw [toReal_maximum]
  rcases le_total 0 (toReal a) with ha | ha
  · exact le_trans (le_trans (mul_le_mul_of_nonneg_left he₂ ha) (mul_le_mulUp a hi))
      (le_max_right _ _)
  · exact le_trans (le_trans (mul_le_mul_of_nonpos_left he₁ ha) (mul_le_mulUp a lo))
      (le_max_left _ _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.dualBound_le {S : SpectraShadow 𝕋 (Vec 𝕋 n)} {a : Vec 𝕋 n} {Y : Mat 𝕋 S.k S.k}
    (h : S.dualCertified a Y = true) :
    ∀ x ∈ S.construct, ∑ r, toReal (a r) * x r ≤ toReal (S.dualBound a Y) := by -- --- PROOF ---
  simp only [SpectraShadow.dualCertified, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hsym, hdom⟩, heq⟩, -⟩ := h
  rintro _ ⟨y, hy, e, he, rfl⟩
  obtain ⟨β, hP, hyβ⟩ := SpectraShadow.mem_nominalSet_iff.mp hy
  -- `Y` read as reals is positive semidefinite
  have hY : (toRealMat Y).PosSemidef := by
    refine SpectraShadow.posSemidef_of_diagDominant _ (fun i j =>
      le_antisymm (toReal_le_of_le (hsym j i)) (toReal_le_of_le (hsym i j))) fun i => ?_
    refine le_trans (le_trans (Finset.sum_le_sum fun j _ => ?_) (sum_le_sumUp _))
      (toReal_le_of_le (hdom i))
    by_cases hj : j = i
    · simp [hj, toReal_zero]
    · simp [hj, toRealMat, toReal_absolute]
  -- the equalities, read as reals
  have htr : ∀ l, (toRealMat (S.A l) * toRealMat Y).trace
      = -∑ r, toReal (a r) * toReal (S.G l r) := fun l => by
    have := congrArg (fun q : ℚ => (q : ℝ)) (heq l)
    simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_neg, toReal_toRat] at this
    simpa [Matrix.trace, Matrix.mul_apply, toRealMat] using this
  -- weak duality on the nominal part: `aᵀ G β ≤ tr(A₀ Y)`
  have h0 := CORALean.Real.SpectraShadow.trace_mul_nonneg hP hY
  rw [Matrix.add_mul, Matrix.trace_add, Matrix.sum_mul, Matrix.trace_sum] at h0
  simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, htr, mul_neg,
    Finset.sum_neg_distrib] at h0
  have hdual : ∑ j, β j * ∑ r, toReal (a r) * toReal (S.G j r)
      ≤ (toRealMat S.A₀ * toRealMat Y).trace := by linarith
  -- the rounded-up parts of the bound
  have htrA : (toRealMat S.A₀ * toRealMat Y).trace
      = ∑ r, ∑ j, toReal (S.A₀ r j) * toReal (Y j r) := by
    simp [Matrix.trace, Matrix.mul_apply, toRealMat]
  have hsumtr : ∑ r, ∑ j, toReal (S.A₀ r j) * toReal (Y j r)
      ≤ toReal (sumUp fun r => dotUp (fun j => S.A₀ r j) fun j => Y j r) :=
    le_trans (Finset.sum_le_sum fun r _ => le_dotUp _ _) (sum_le_sumUp _)
  have hc := le_dotUp a S.c
  have hbox : ∑ r, toReal (a r) * e r ≤ toReal (sumUp fun r =>
      maximum (mulUp (a r) (S.I_error.inf r)) (mulUp (a r) (S.I_error.sup r))) := by
    refine le_trans (Finset.sum_le_sum fun r _ => ?_) (sum_le_sumUp _)
    have hb : toReal (S.I_error.inf r) ≤ e r ∧ e r ≤ toReal (S.I_error.sup r) := he r
    exact SpectraShadow.aux_mul_le_corner _ _ _ hb.1 hb.2
  -- the point's value along `a`, split into centre, generators and error
  have hsplit : ∑ r, toReal (a r) * (y + e) r = ∑ r, toReal (a r) * toReal (S.c r)
      + ∑ j, β j * ∑ r, toReal (a r) * toReal (S.G j r) + ∑ r, toReal (a r) * e r := by
    have hgen : ∑ r, toReal (a r) * ∑ j, toReal (S.G j r) * β j
        = ∑ j, β j * ∑ r, toReal (a r) * toReal (S.G j r) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun r _ => by ring
    simp only [Pi.add_apply, hyβ, mul_add, Finset.sum_add_distrib, hgen]
  have s₁ := add_le_addUp (dotUp a S.c) (sumUp fun r => dotUp (fun j => S.A₀ r j) fun j => Y j r)
  have s₂ := add_le_addUp (addUp (dotUp a S.c)
    (sumUp fun r => dotUp (fun j => S.A₀ r j) fun j => Y j r))
    (sumUp fun r => maximum (mulUp (a r) (S.I_error.inf r)) (mulUp (a r) (S.I_error.sup r)))
  simp only [SpectraShadow.dualBound]
  rw [hsplit]
  linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
