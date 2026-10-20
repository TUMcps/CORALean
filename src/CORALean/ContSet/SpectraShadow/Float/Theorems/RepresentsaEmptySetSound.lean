module

public import CORALean.ContSet.SpectraShadow.Float.Operations.RepresentsaEmptySet
public import CORALean.ContSet.SpectraShadow.Float.Theorems.MemNominalSet
public import CORALean.ContSet.SpectraShadow.Float.Theorems.PosSemidefOfDiagDominant
public import CORALean.ContSet.SpectraShadow.Real.Theorems.TraceMulNonneg

@[expose] public section

/-!
# A `true` from `SpectraShadow.representsa_emptySet` proves the set empty

A member would give a `β` with the inequality's matrix `⪰ 0`; against the semidefinite `Y` its
trace is nonnegative, but it is `tr(A₀ Y) + Σ βₗ tr(Aₗ Y) = tr(A₀ Y) < 0`.

## Inputs
* `S` – spectrahedral shadow
* `Y` – `S.k × S.k` matrix

## Hypotheses
* `h` – `S.representsa_emptySet Y` holds

## Conclusion
* A `true` from `SpectraShadow.representsa_emptySet` proves the set empty
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic ToRat InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.representsa_emptySet_sound {S : SpectraShadow 𝕋 (Vec 𝕋 n)} {Y : Mat 𝕋 S.k S.k}
    (h : S.representsa_emptySet Y = true) : -- --- CONCL ---
    S.construct = ∅ := by -- --- PROOF ---
  simp only [SpectraShadow.representsa_emptySet, SpectraShadow.dualCertified, Bool.and_eq_true,
    List.all_eq_true, List.mem_finRange, forall_const, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hsym, hdom⟩, heq⟩, -⟩, hneg⟩, -⟩ := h
  refine Set.eq_empty_of_forall_notMem fun x hx => ?_
  obtain ⟨y, hy, -, -, -⟩ := hx
  obtain ⟨β, hP, -⟩ := SpectraShadow.mem_nominalSet_iff.mp hy
  -- `Y` read as reals is positive semidefinite
  have hY : (toRealMat Y).PosSemidef := by
    refine SpectraShadow.posSemidef_of_diagDominant _ (fun i j =>
      le_antisymm (toReal_le_of_le (hsym j i)) (toReal_le_of_le (hsym i j))) fun i => ?_
    refine le_trans (le_trans (Finset.sum_le_sum fun j _ => ?_) (sum_le_sumUp _))
      (toReal_le_of_le (hdom i))
    by_cases hj : j = i
    · simp [hj, toReal_zero]
    · simp [hj, toRealMat, toReal_absolute]
  -- the coefficient traces vanish and the constant one is negative, read as reals
  have htr : ∀ l, (toRealMat (S.A l) * toRealMat Y).trace = 0 := fun l => by
    have := congrArg (fun q : ℚ => (q : ℝ)) (heq l)
    simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_neg, toReal_toRat, toReal_zero, zero_mul,
      Finset.sum_const_zero, neg_zero] at this
    simpa [Matrix.trace, Matrix.mul_apply, toRealMat] using this
  have htr0 : (toRealMat S.A₀ * toRealMat Y).trace < 0 := by
    have := (Rat.cast_lt (K := ℝ)).mpr hneg
    simp only [Rat.cast_sum, Rat.cast_mul, toReal_toRat, Rat.cast_zero] at this
    simpa [Matrix.trace, Matrix.mul_apply, toRealMat] using this
  -- weak duality: the trace against `Y` is nonnegative, and it is `tr(A₀ Y)`
  have h0 := CORALean.Real.SpectraShadow.trace_mul_nonneg hP hY
  rw [Matrix.add_mul, Matrix.trace_add, Matrix.sum_mul, Matrix.trace_sum] at h0
  simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, htr, mul_zero,
    Finset.sum_const_zero, add_zero] at h0
  linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
