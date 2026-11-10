module

public import CORALean.ContSet.Interval.Float.Operations.Tan
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

@[expose] public section

/-!
# `Interval.tan` contains the image under `tan`

For every box, with no hypothesis. A coordinate is bounded only where the cosine has one strict
sign at both ends of a range shorter than `π`, which leaves no zero of the cosine between, so the
tangent is monotone there; every other coordinate is unbounded, and the box holds every value,
the tangent at a pole (`0` in Lean) included.

## Inputs
* `p` – halving count
* `I` – interval box

## Hypotheses
* none

## Conclusion
* the tangent image of `I` lies in the result box
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   03-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- No zero of the cosine between two points of one strict sign of it less than `π` apart. -/
private theorem aux_cos_ne_zero_of_same_sign {l u x : ℝ} (h1 : l ≤ x) (h2 : x ≤ u)
    (hw : u - l < Real.pi) (hs : 0 < Real.cos l * Real.cos u) : -- --- CONCL ---
    Real.cos x ≠ 0 := by -- --- PROOF ---
  intro hx
  have ha : 0 ≤ Real.sin (x - l) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hb : 0 ≤ Real.sin (u - x) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have e1 : Real.cos l = Real.sin x * Real.sin (x - l) := by
    have : l = x - (x - l) := by ring
    conv_lhs => rw [this, Real.cos_sub, hx]
    ring
  have e2 : Real.cos u = -(Real.sin x * Real.sin (u - x)) := by
    have : u = x + (u - x) := by ring
    conv_lhs => rw [this, Real.cos_add, hx]
    ring
  have hsq : Real.sin x ^ 2 = 1 := by
    have := Real.sin_sq_add_cos_sq x
    rw [hx] at this
    linarith
  rw [e1, e2] at hs
  have : Real.cos l * Real.cos u = -(Real.sin x ^ 2 * (Real.sin (x - l) * Real.sin (u - x))) := by
    rw [e1, e2]; ring
  nlinarith [mul_nonneg ha hb]

/-- The tangent is monotone on a range shorter than `π` whose ends have a cosine of one strict
sign. -/
private theorem aux_tan_monotoneOn {l u : ℝ} (hw : u - l < Real.pi)
    (hs : 0 < Real.cos l * Real.cos u) : -- --- CONCL ---
    MonotoneOn Real.tan (Set.Icc l u) := by -- --- PROOF ---
  have hne : ∀ x ∈ Set.Icc l u, Real.cos x ≠ 0 := fun x hx =>
    aux_cos_ne_zero_of_same_sign hx.1 hx.2 hw hs
  refine monotoneOn_of_deriv_nonneg (convex_Icc l u)
    (Real.continuousOn_tan.mono fun x hx => hne x hx)
    (fun x hx => (Real.hasDerivAt_tan (hne x (interior_subset hx))).differentiableAt
      |>.differentiableWithinAt) fun x hx => ?_
  rw [(Real.hasDerivAt_tan (hne x (interior_subset hx))).deriv]
  positivity

/-- The bounds of one coordinate, whatever branch `Interval.step_tanBranch` certifies. -/
private theorem aux_tan_bounds [SoundFloatArithmetic 𝕋] (p : ℕ) {l u : 𝕋} {x : ℝ}
    (h1 : toReal l ≤ x) (h2 : x ≤ toReal u) : -- --- CONCL ---
    (∀ a, (match Interval.step_tanBranch p l u with
        | some true => some (tanDown p l)
        | some false => some (tanDownNeg p l)
        | none => none) = some a → toReal a ≤ Real.tan x) ∧
    (∀ b, (match Interval.step_tanBranch p l u with
        | some true => some (tanUp p u)
        | some false => some (tanUpNeg p u)
        | none => none) = some b → Real.tan x ≤ toReal b) := by -- --- PROOF ---
  have hx : x ∈ Set.Icc (toReal l) (toReal u) := ⟨h1, h2⟩
  have hl : toReal l ∈ Set.Icc (toReal l) (toReal u) := ⟨le_rfl, le_trans h1 h2⟩
  have hu : toReal u ∈ Set.Icc (toReal l) (toReal u) := ⟨le_trans h1 h2, le_rfl⟩
  -- the range is certified shorter than `π`, and the cosine has one sign at both ends
  unfold Interval.step_tanBranch
  by_cases hw : ltStrict (subUp u l) piBelow = true
  · have hw' : toReal u - toReal l < Real.pi :=
      lt_of_le_of_lt (sub_le_subUp u l) (lt_trans (toReal_lt_of_ltStrict hw) piBelow_lt_pi)
    rw [if_pos hw]
    -- positive branch: `tanDown`/`tanUp` and the monotone tangent
    by_cases hp : ltStrict zero (cosDown p l) = true ∧ ltStrict zero (cosDown p u) = true
    · rw [if_pos hp]
      have c1 : 0 < toReal (cosDown p l) := by
        simpa [toReal_zero] using toReal_lt_of_ltStrict hp.1
      have c2 : 0 < toReal (cosDown p u) := by
        simpa [toReal_zero] using toReal_lt_of_ltStrict hp.2
      have hs : 0 < Real.cos (toReal l) * Real.cos (toReal u) :=
        mul_pos (lt_of_lt_of_le c1 (cosDown_le p l)) (lt_of_lt_of_le c2 (cosDown_le p u))
      have hm := aux_tan_monotoneOn hw' hs
      exact ⟨fun a ha => by
          cases ha
          exact le_trans (tanDown_le p l c1) (hm hl hx h1),
        fun b hb => by
          cases hb
          exact le_trans (hm hx hu h2) (le_tanUp p u c2)⟩
    · rw [if_neg hp]
      -- negative branch: `tanDownNeg`/`tanUpNeg`, the same argument with the cosine negated
      by_cases hq : ltStrict (cosUp p l) zero = true ∧ ltStrict (cosUp p u) zero = true
      · rw [if_pos hq]
        have c1 : toReal (cosUp p l) < 0 := by
          simpa [toReal_zero] using toReal_lt_of_ltStrict hq.1
        have c2 : toReal (cosUp p u) < 0 := by
          simpa [toReal_zero] using toReal_lt_of_ltStrict hq.2
        have hs : 0 < Real.cos (toReal l) * Real.cos (toReal u) :=
          mul_pos_of_neg_of_neg (lt_of_le_of_lt (le_cosUp p l) c1)
            (lt_of_le_of_lt (le_cosUp p u) c2)
        have hm := aux_tan_monotoneOn hw' hs
        exact ⟨fun a ha => by
            cases ha
            exact le_trans (tanDownNeg_le p l c1) (hm hl hx h1),
          fun b hb => by
            cases hb
            exact le_trans (hm hx hu h2) (le_tanUpNeg p u c2)⟩
      · -- neither sign is certified: no bound is returned
        rw [if_neg hq]
        exact ⟨fun a ha => by simp at ha, fun b hb => by simp at hb⟩
  · -- the range is not certified short: no bound is returned
    rw [if_neg hw]
    exact ⟨fun a ha => by simp at ha, fun b hb => by simp at hb⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every coordinate is bounded only where the range is certified free of poles, so the box holds
the tangent of every point of `I`, a pole included. -/
theorem Interval.tan_outer [SoundFloatArithmetic 𝕋] (p : ℕ) (I : Interval (Vec 𝕋 n)) :
    (fun x i => Real.tan (x i)) '' I.toSet ⊆ (I.tan p).toSet := by
  rintro _ ⟨x, hx, rfl⟩ i
  have hx' : toReal (I.inf i) ≤ x i ∧ x i ≤ toReal (I.sup i) := hx i
  have hb := aux_tan_bounds p hx'.1 hx'.2
  exact ⟨fun a ha => hb.1 a ha, fun b hb' => hb.2 b hb'⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
