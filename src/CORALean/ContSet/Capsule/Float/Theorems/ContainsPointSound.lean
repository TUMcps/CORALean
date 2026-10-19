module

public import CORALean.ContSet.Capsule.Float.Operations.ContainsPoint
public import CORALean.ContSet.Capsule.Float.Theorems.MemConstructOfSplit
public import CORALean.ContSet.Interval.Float.Theorems.Basic

@[expose] public section

/-!
# `Capsule.containsPoint` is sound

A `true` answer exhibits the clipped parameter `t ∈ [-1, 1]`, a point `e` of the box (the clamp of
`-(c + t g - p)` to the box's range in each coordinate, which a nonempty box admits) and a
certified bound on the length of the rest, `p - (c + t g) - e`: its squared length rounded up is at
most `r²` rounded down, with `r ≥ 0`. So the point is in the capsule. `false` refutes nothing.

## Inputs
* `C` – capsule
* `p` – float point

## Hypotheses
* `h` – `containsPoint` answers true

## Conclusion
* the point lies in the capsule
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open CORALean FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The clamp `e` of `u` to `[a, b]` is in the range, and `|u - e|` is at most the larger of
`0`, `a - u` and `u - b`. -/
theorem Capsule.aux_clamp {a b u : ℝ} (hab : a ≤ b) :
    (a ≤ max a (min b u) ∧ max a (min b u) ≤ b) ∧
      |u - max a (min b u)| ≤ max 0 (max (a - u) (u - b)) := by -- --- PROOF ---
  refine ⟨⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩, ?_⟩
  rcases le_total u b with hb | hb
  · rw [min_eq_right hb]
    rcases le_total a u with ha | ha
    · rw [max_eq_right ha, sub_self, abs_zero]
      exact le_max_left _ _
    · rw [max_eq_left ha, abs_of_nonpos (by linarith)]
      exact le_trans (by linarith) (le_trans (le_max_left _ _) (le_max_right _ _))
  · rw [min_eq_left hb, max_eq_right hab, abs_of_nonneg (by linarith)]
    exact le_trans (le_max_right _ _) (le_max_right _ _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.containsPoint_sound {C : Capsule 𝕋 n} {p : Vec 𝕋 n}
    (h : C.containsPoint p = true) : toRealVec p ∈ C.construct := by -- --- PROOF ---
  unfold Capsule.containsPoint at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const] at h
  obtain ⟨⟨hI, hr⟩, hsq⟩ := h
  have hr0 : 0 ≤ toReal C.r := by simpa [toReal_zero] using toReal_le_of_le hr
  -- the clipped parameter lies in `[-1, 1]`
  set t := maximum (neg (one : 𝕋)) (minimum one
    (divUp (dotUp (fun i => subUp (p i) (C.c i)) C.g) (dotUp C.g C.g))) with ht
  have ht1 : toReal t ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [ht, toReal_maximum, toReal_neg, toReal_one, toReal_minimum, toReal_one]
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  -- the vector `c + t g - p`, and its clamp into the box
  set v : Vec ℝ n := fun j => toReal (C.c j) + toReal t * toReal (C.g j) - toReal (p j)
  set e : Vec ℝ n := fun j =>
    max (toReal (C.I_error.inf j)) (min (toReal (C.I_error.sup j)) (-v j))
  have hab : ∀ j, toReal (C.I_error.inf j) ≤ toReal (C.I_error.sup j) :=
    fun j => toReal_le_of_le (hI j)
  refine Capsule.mem_construct_of_split C ht1 (w := fun j => -v j - e j) ?_ ?_
  · -- each entry is below the magnitude the directed arithmetic bracketed
    refine le_trans (norm₂_le_of_sq_le (fun j => ?_) (toReal_le_of_le hsq)) ?_
    · have h1 := subDown_le_sub (addDown (C.c j) (mulDown t (C.g j))) (p j)
      have h2 := sub_le_subUp (addUp (C.c j) (mulUp t (C.g j))) (p j)
      have h3 := addDown_le_add (C.c j) (mulDown t (C.g j))
      have h4 := add_le_addUp (C.c j) (mulUp t (C.g j))
      have h5 := mulDown_le_mul t (C.g j)
      have h6 := mul_le_mulUp t (C.g j)
      have h7 := add_le_addUp (C.I_error.inf j) (subUp (addUp (C.c j) (mulUp t (C.g j))) (p j))
      have h8 := addDown_le_add (subDown (addDown (C.c j) (mulDown t (C.g j))) (p j))
        (C.I_error.sup j)
      have hc := (Capsule.aux_clamp (u := -v j) (hab j)).2
      refine le_trans hc ?_
      simp only [toReal_maximum, toReal_neg, toReal_zero]
      refine max_le_max le_rfl (max_le_max ?_ ?_)
      · simp only [v]; linarith
      · simp only [v]; linarith
    · rw [toReal_absolute, abs_of_nonneg hr0]
  · -- what is left is the clamp, in the box
    refine Interval.mem_vec_iff.mpr fun j => ?_
    have hc := (Capsule.aux_clamp (u := -v j) (hab j)).1
    have hx : (toRealVec p - (toRealVec C.c + toReal t • toRealVec C.g + fun j => -v j - e j)) j
        = e j := by
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, toRealVec, v]
      ring
    rw [hx]
    exact hc

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
