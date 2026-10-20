module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.QuadTermLoFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.QuadTermLo
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.QuadTermBetween
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.VertexSign
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.QuadTermFloat

@[expose] public section

/-!
# The float `quadTermLo` is at most the exact one

When the box is certified off the vertex the exact `if` takes its `min` branch, which the two
endpoint lower bounds undercut. Otherwise the float returns `-1/2`, which `γ` never goes below,
so it is below either branch of the exact one.

## Inputs
* `t` – float time
* `a` – float box lower end
* `b` – float box upper end

## Hypotheses
* none

## Conclusion
* the float lower value is at most the exact least value
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

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


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.quadTermLo_le (t a b : 𝕋) : -- --- CONCL ---
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
    exact min_le_min (MatExp.quadTerm_mem t a).1 (MatExp.quadTerm_mem t b).1
  · -- not certified: `-1/2` is under `γ` everywhere, so under either exact branch
    rw [toReal_neg, toReal_half, toReal_one]
    have := aux_quadTermLo_ge (toReal t) (toReal a) (toReal b)
    linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
