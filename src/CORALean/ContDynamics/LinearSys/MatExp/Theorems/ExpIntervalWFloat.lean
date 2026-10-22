module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalWFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalWOuter
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.HalfSqBoundsFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.QuadTermHiFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.QuadTermHi
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.QuadTermFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.QuadTerm
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.QuadTermLoFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.QuadTermLo
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.QuadTermBetween
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.VertexSign
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

## Inputs
* `A` – float interval matrix
* `t` – float time
* `M` – member matrix

## Hypotheses
* `hM` – member lies in the interval matrix

## Conclusion
* the member's second-order term lies in the float interval matrix
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- `γ(a)` lies in `quadTerm t a`. -/
theorem MatExp.aux_quadTerm_mem (t a : 𝕋) : -- --- CONCL ---
    toReal (MatExp.quadTerm t a).inf ≤ Real.MatExp.quadTerm (toReal t) (toReal a)
      ∧ Real.MatExp.quadTerm (toReal t) (toReal a) ≤
        toReal (MatExp.quadTerm t a).sup := by -- --- PROOF ---
  have hm1 := mulDown_le_mul a t
  have hm2 := mul_le_mulUp a t
  have hsq := Interval.mul_between_corners hm1 hm2 hm1 hm2
  have hγ : Real.MatExp.quadTerm (toReal t) (toReal a)
      = toReal a * toReal t + (toReal a * toReal t) * (toReal a * toReal t) / 2 := by
    simp only [Real.MatExp.quadTerm]; ring
  rw [hγ]
  simp only [MatExp.quadTerm]
  constructor
  · refine le_trans (addDown_le_add _ _) ?_
    rw [toReal_half]
    linarith [hsq.1]
  · refine le_trans ?_ (add_le_addUp _ _)
    rw [toReal_half]
    linarith [hsq.2]

end


section
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- `γ x + 1/2 = (x t + 1)² / 2`. -/
theorem aux_quadTerm_ge (t x : ℝ) : -(1 / 2) ≤ Real.MatExp.quadTerm t x := by
  have : (0:ℝ) ≤ (x * t + 1) ^ 2 := sq_nonneg _
  simp only [Real.MatExp.quadTerm]
  nlinarith


/-- `-1/2` is below the exact lower bound, whichever branch it takes. -/
theorem aux_quadTermLo_ge (t a b : ℝ) : -(1 / 2) ≤ Real.MatExp.quadTermLo t a b := by
  rw [Real.MatExp.quadTermLo]
  split
  · exact le_rfl
  · exact le_min (aux_quadTerm_ge t a) (aux_quadTerm_ge t b)


/-- A positive `t + c t²` puts `c` right of the vertex, so the vertex test fails. -/
theorem aux_not_straddle_left {t a b : ℝ} (h : 0 < t + a * t ^ 2) :
    ¬ (a ≤ -1 / t ∧ -1 / t ≤ b) := by
  rintro ⟨ha, -⟩
  rw [Real.MatExp.vertex_sign] at h
  nlinarith [sq_nonneg t]


/-- A negative `t + c t²` puts `c` left of the vertex. -/
theorem aux_not_straddle_right {t a b : ℝ} (h : t + b * t ^ 2 < 0) :
    ¬ (a ≤ -1 / t ∧ -1 / t ≤ b) := by
  rintro ⟨-, hb⟩
  rw [Real.MatExp.vertex_sign] at h
  nlinarith [sq_nonneg t]


/-- The float `quadTermLo` is at most the exact one. -/
theorem MatExp.aux_quadTermLo_le (t a b : 𝕋) : -- --- CONCL ---
    toReal (MatExp.quadTermLo t a b)
      ≤ Real.MatExp.quadTermLo (toReal t) (toReal a) (toReal b) := by -- --- PROOF ---
  -- `a t²` and `b t²` are bracketed by the corner hull of the directed `t²`
  have hsq := Interval.mul_between_corners (le_refl (toReal a)) (le_refl (toReal a))
    (mulDown_le_mul t t) (mul_le_mulUp t t)
  have hsq' := Interval.mul_between_corners (le_refl (toReal b)) (le_refl (toReal b))
    (mulDown_le_mul t t) (mul_le_mulUp t t)
  simp only [MatExp.quadTermLo]
  split
  · -- certified off the vertex: the exact `if` takes its `min` branch
    rename_i hc
    rw [Real.MatExp.quadTermLo]
    have hnot : ¬ (toReal a ≤ -1 / toReal t ∧ -1 / toReal t ≤ toReal b) := by
      rcases Bool.or_eq_true_iff.mp hc with h | h
      · have h1 := toReal_lt_of_ltStrict h
        rw [toReal_zero] at h1
        refine aux_not_straddle_left ?_
        have := addDown_le_add t (Interval.mulLo a a (mulDown t t) (mulUp t t))
        nlinarith [hsq.1]
      · have h1 := toReal_lt_of_ltStrict h
        rw [toReal_zero] at h1
        refine aux_not_straddle_right ?_
        have := add_le_addUp t (Interval.mulHi b b (mulDown t t) (mulUp t t))
        nlinarith [hsq'.2]
    -- the `min` of the endpoint lower bounds undercuts the exact `min`
    rw [if_neg hnot, toReal_minimum]
    exact min_le_min (MatExp.aux_quadTerm_mem t a).1 (MatExp.aux_quadTerm_mem t b).1
  · -- not certified: `-1/2` is under `γ` everywhere, so under either exact branch
    rw [toReal_neg, toReal_half, toReal_one]
    have := aux_quadTermLo_ge (toReal t) (toReal a) (toReal b)
    linarith

end


section
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- The float `quadTermHi` is at least the exact one. -/
theorem MatExp.aux_quadTermHi_ge (t a b : 𝕋) :
    Real.MatExp.quadTermHi (toReal t) (toReal a) (toReal b) ≤
      toReal (MatExp.quadTermHi t a b) := by
  rw [MatExp.quadTermHi, toReal_maximum, Real.MatExp.quadTermHi]
  exact max_le_max (MatExp.aux_quadTerm_mem t a).2 (MatExp.aux_quadTerm_mem t b).2

end


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
    (hf' : toReal t + toReal t ^ 2 / 2 * (M i i + M j j) ≤ toReal fHi) : -- --- CONCL ---
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
    exact ⟨le_trans (MatExp.aux_quadTermLo_le t _ _) hb.1, le_trans hb.2 (MatExp.aux_quadTermHi_ge t
      _ _)⟩
  · simp only [if_neg h]
    exact Interval.mul_between_corners (hm i j).1 (hm i j).2 hf hf'


/-- The directed sums of the corner hulls bracket the `k ≠ i, j` row-column sum. -/
theorem aux_rowColSum_mem (A : Interval (Mat 𝕋 n n)) {M : Mat ℝ n n} (hM : M ∈ A.construct)
    (i j : Fin n) : -- --- CONCL ---
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
    {M : Mat ℝ n n} (hM : M ∈ A.construct) : -- --- CONCL ---
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
  have hf : toReal (addDown t (Interval.mulLo ht.inf ht.sup sLo sHi))
      ≤ toReal t + toReal t ^ 2 / 2 * (M i i + M j j) :=
    le_trans (addDown_le_add _ _) (by linarith [hsh.1])
  have hf' : toReal t + toReal t ^ 2 / 2 * (M i i + M j j)
      ≤ toReal (addUp t (Interval.mulHi ht.inf ht.sup sLo sHi)) :=
    le_trans (by linarith [hsh.2]) (add_le_addUp _ _)
  -- the leading summand: a single-use product off the diagonal, the parabola on it
  have hfirst := aux_leading_mem A t hm hf hf'
  rw [Real.MatExp.expW_apply]
  exact ⟨le_trans (addDown_le_add _ _) (add_le_add hfirst.1 hSh.1),
    le_trans (add_le_add hfirst.2 hSh.2) (add_le_addUp _ _)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
