module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalWFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalWOuter
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.HalfSqBoundsFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.QuadTermHiFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.QuadTermLoFloat
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners

@[expose] public section

/-!
# `W(t)` of every member of a float interval matrix lies in `expIntervalW`

The float counterpart of `Real.MatExp.expW_mem_expIntervalW`, by the same three pieces: the
single-use product off the diagonal, the parabola on it, and the `k ≠ i, j` sum. Each exact
bound is replaced by its rounded bracket, and the corner hull of two brackets holds the
product of the two reals they hold.

The time is a float `t`, read as `toReal t`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A sum with two indices zeroed is the sum over the rest. -/
theorem aux_sum_ite_excl (g : Fin n → ℝ) (i j : Fin n) :
    ∑ k, (if k = i ∨ k = j then 0 else g k)
      = ∑ k ∈ Finset.univ \ ({i, j} : Finset (Fin n)), g k := by
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext k
  simp

/-- The leading summand: a single-use product off the diagonal, the parabola on it. -/
theorem aux_leading_mem (A : Interval (Mat 𝕋 n n)) (t : 𝕋) {M : Mat ℝ n n}
    (hm : ∀ i j, toReal (A.inf i j) ≤ M i j ∧ M i j ≤ toReal (A.sup i j))
    {fLo fHi : 𝕋} {i j : Fin n}
    (hf : toReal fLo ≤ toReal t + toReal t ^ 2 / 2 * (M i i + M j j))
    (hf' : toReal t + toReal t ^ 2 / 2 * (M i i + M j j) ≤ toReal fHi) :
    toReal (if i = j then MatExp.quadTermLo t (A.inf i i) (A.sup i i)
        else Interval.mulLo (A.inf i j) (A.sup i j) fLo fHi)
      ≤ (if i = j then Real.MatExp.quadTerm (toReal t) (M i i)
        else M i j * (toReal t + toReal t ^ 2 / 2 * (M i i + M j j)))
    ∧ (if i = j then Real.MatExp.quadTerm (toReal t) (M i i)
        else M i j * (toReal t + toReal t ^ 2 / 2 * (M i i + M j j)))
      ≤ toReal (if i = j then MatExp.quadTermHi t (A.inf i i) (A.sup i i)
        else Interval.mulHi (A.inf i j) (A.sup i j) fLo fHi) := by -- --- PROOF ---
  by_cases h : i = j
  · -- on the diagonal the parabola's bounds, rounded, hold `γ`
    subst h
    simp only [reduceIte]
    have hb := Real.MatExp.quadTerm_between (t := toReal t) (hm i i).1 (hm i i).2
    exact ⟨le_trans (MatExp.quadTermLo_le t _ _) hb.1, le_trans hb.2 (MatExp.quadTermHi_ge t _ _)⟩
  · simp only [if_neg h]
    exact Interval.mul_between_corners (hm i j).1 (hm i j).2 hf hf'


/-- The directed sums of the corner hulls bracket the `k ≠ i, j` row-column sum. -/
theorem aux_rowColSum_mem (A : Interval (Mat 𝕋 n n)) {M : Mat ℝ n n} (hM : M ∈ A.construct)
    (i j : Fin n) :
    toReal (sumDown fun k => if k = i ∨ k = j then (zero : 𝕋)
        else Interval.mulLo (A.inf i k) (A.sup i k) (A.inf k j) (A.sup k j))
      ≤ ∑ k ∈ Finset.univ \ ({i, j} : Finset (Fin n)), M i k * M k j
    ∧ ∑ k ∈ Finset.univ \ ({i, j} : Finset (Fin n)), M i k * M k j
      ≤ toReal (sumUp fun k => if k = i ∨ k = j then (zero : 𝕋)
        else Interval.mulHi (A.inf i k) (A.sup i k) (A.inf k j) (A.sup k j)) := by -- --- PROOF ---
  have hm := Interval.mem_mat_iff.mp hM
  -- the lower bound by `sumDown_le_sum`, the upper by `sum_le_sumUp`, term by term
  constructor
  · refine le_trans (sumDown_le_sum _) ?_
    rw [← aux_sum_ite_excl]
    refine Finset.sum_le_sum fun k _ => ?_
    by_cases hk : k = i ∨ k = j
    · simp [hk, toReal_zero]
    · simp only [hk, if_false]
      exact (Interval.mul_between_corners (hm i k).1 (hm i k).2 (hm k j).1 (hm k j).2).1
  · refine le_trans ?_ (sum_le_sumUp _)
    rw [← aux_sum_ite_excl]
    refine Finset.sum_le_sum fun k _ => ?_
    by_cases hk : k = i ∨ k = j
    · simp [hk, toReal_zero]
    · simp only [hk, if_false]
      exact (Interval.mul_between_corners (hm i k).1 (hm i k).2 (hm k j).1 (hm k j).2).2


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.expW_mem_expIntervalW (A : Interval (Mat 𝕋 n n)) (t : 𝕋)
    {M : Mat ℝ n n} (hM : M ∈ A.construct) :
    Real.MatExp.expW M (toReal t) ∈ (MatExp.expIntervalW A t).construct := by -- --- PROOF ---
  refine Interval.mem_mat_iff.mpr fun i j => ?_
  have hm := Interval.mem_mat_iff.mp hM
  -- the bracket of `½ t²`, and the bracketed `k ≠ i, j` row-column sum under it
  have hh := MatExp.halfSqBounds_mem t
  set ht := MatExp.halfSqBounds t with hht
  have hS := aux_rowColSum_mem A hM i j
  have hSh := Interval.mul_between_corners hh.1 hh.2 hS.1 hS.2
  -- the diagonal sum `A i i + A j j`, and the factor `t + ½ t² (A i i + A j j)` it feeds
  set sLo := addDown (A.inf i i) (A.inf j j) with hsLo
  set sHi := addUp (A.sup i i) (A.sup j j) with hsHi
  have hs : toReal sLo ≤ M i i + M j j ∧ M i i + M j j ≤ toReal sHi :=
    ⟨le_trans (addDown_le_add _ _) (add_le_add (hm i i).1 (hm j j).1),
     le_trans (add_le_add (hm i i).2 (hm j j).2) (add_le_addUp _ _)⟩
  have hsh := Interval.mul_between_corners hh.1 hh.2 hs.1 hs.2
  have hf : toReal (addDown t (Interval.mulLo ht.1 ht.2 sLo sHi))
      ≤ toReal t + toReal t ^ 2 / 2 * (M i i + M j j) :=
    le_trans (addDown_le_add _ _) (by linarith [hsh.1])
  have hf' : toReal t + toReal t ^ 2 / 2 * (M i i + M j j)
      ≤ toReal (addUp t (Interval.mulHi ht.1 ht.2 sLo sHi)) :=
    le_trans (by linarith [hsh.2]) (add_le_addUp _ _)
  -- the leading summand: a single-use product off the diagonal, the parabola on it
  have hfirst := aux_leading_mem A t hm hf hf'
  rw [Real.MatExp.expW_apply]
  exact ⟨le_trans (addDown_le_add _ _) (add_le_add hfirst.1 hSh.1),
    le_trans (add_le_add hfirst.2 hSh.2) (add_le_addUp _ _)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
