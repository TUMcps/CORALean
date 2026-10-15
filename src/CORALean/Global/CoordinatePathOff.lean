module

public import CORALean.Global.CoordinatePath

@[expose] public section

/-!
# Moving only some coordinates from the center of a box

[1, Thm. 2]'s outer bound moves the disturbances `w` of `f(w, u)` with the controls `u` at
the center of their interval, and bounds `∂ⱼf` only there. With the inputs one vector and
the controls an index predicate `E`, a point of the box whose `E` coordinates are at the
center is a move from the center through the other coordinates only, each bounded by
`Uⱼ`, where `|∂ⱼf| ≤ Uⱼ` is asked only at points with their `E` coordinates at the center.
The reduction is [`abs_sub_le_sum_of_abs_partial_le`](CoordinatePath.lean) applied to `f`
with the `E` coordinates pinned to the center.

## References

* [1] E. Goubault and S. Putot. "Robust Under-Approximations and Application to
      Reachability of Non-Linear Control Systems With Disturbances". IEEE Control Systems
      Letters, 4(4):928-933, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set

variable {m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `f` moves from the center by at most `Σ_{j ∉ E} Uⱼ rⱼ` to a point with its `E` coordinates
at the center, when `|∂ⱼf| ≤ Uⱼ` for `j ∉ E` at the points of the box with `E` at the center. -/
theorem abs_sub_le_sum_filter_of_abs_partial_le {f : (Fin m → ℝ) → ℝ} (hf : Differentiable ℝ f)
    {lo hi : Fin m → ℝ} (hlh : lo ≤ hi) (E : Fin m → Prop) [DecidablePred E] (U : Fin m → ℝ)
    (hU : ∀ y ∈ Icc lo hi, (∀ j, E j → y j = (lo j + hi j) / 2) → ∀ j, ¬ E j →
      |fderiv ℝ f y (Pi.single j 1)| ≤ U j) {x : Fin m → ℝ} (hx : x ∈ Icc lo hi)
    (hxE : ∀ j, E j → x j = (lo j + hi j) / 2) :
    |f x - f (fun i => (lo i + hi i) / 2)|
      ≤ ∑ j with ¬ E j, U j * ((hi j - lo j) / 2) := by -- --- PROOF ---
  set c : Fin m → ℝ := fun i => (lo i + hi i) / 2 with hc
  -- `f` with the `E` coordinates pinned to the center
  set φ : (Fin m → ℝ) → (Fin m → ℝ) := fun y j => if E j then c j else y j with hφ
  have hφd : Differentiable ℝ φ := differentiable_pi.mpr fun j => by
    by_cases h : E j <;> simp only [hφ, h, if_true, if_false]
    · exact differentiable_const _
    · exact differentiable_apply j
  have hφm : ∀ y ∈ Icc lo hi, φ y ∈ Icc lo hi := fun y hy => ⟨fun j => by
      by_cases h : E j <;> simp only [hφ, h, if_true, if_false, hc]
      · linarith [hlh j]
      · exact hy.1 j, fun j => by
      by_cases h : E j <;> simp only [hφ, h, if_true, if_false, hc]
      · linarith [hlh j]
      · exact hy.2 j⟩
  have hG : Differentiable ℝ (f ∘ φ) := hf.comp hφd
  -- the partial derivatives of the pinned function
  have hpartE : ∀ y i, E i → fderiv ℝ (f ∘ φ) y (Pi.single i 1) = 0 := by
    intro y i hi'
    have h1 := hasDerivAt_comp_update hG y i (y i)
    -- along the line of a pinned coordinate the function is constant
    have h2 : HasDerivAt (fun s => (f ∘ φ) (Function.update y i s)) 0 (y i) := by
      have : (fun s => (f ∘ φ) (Function.update y i s)) = fun _ => (f ∘ φ) y := by
        funext s
        simp only [Function.comp, hφ]
        congr 1
        funext j
        by_cases hj : j = i
        · subst hj; simp [hi']
        · simp [Function.update_of_ne hj]
      rw [this]; exact hasDerivAt_const _ _
    rw [Function.update_eq_self] at h1
    exact h1.unique h2
  -- and a free coordinate sees the partial of `f` at the pinned point
  have hpart : ∀ y i, ¬ E i →
      fderiv ℝ (f ∘ φ) y (Pi.single i 1) = fderiv ℝ f (φ y) (Pi.single i 1) := by
    intro y i hi'
    have h1 := hasDerivAt_comp_update hG y i (y i)
    have h3 := hasDerivAt_comp_update hf (φ y) i (y i)
    have h2 : (fun s => (f ∘ φ) (Function.update y i s))
        = fun s => f (Function.update (φ y) i s) := by
      funext s
      simp only [Function.comp, hφ]
      congr 1
      funext j
      by_cases hj : j = i
      · subst hj; simp [hi']
      · simp [Function.update_of_ne hj]
    -- both lines are the line of `f` through the pinned point
    have h4 : Function.update (φ y) i (y i) = φ y := by
      rw [← Function.update_eq_self i (φ y)]
      simp [hφ, hi']
    rw [Function.update_eq_self] at h1
    rw [h4] at h3
    rw [h2] at h1
    exact h1.unique h3
  -- the existing lemma for `f ∘ φ`, whose pinned partials are `0`
  have := abs_sub_le_sum_of_abs_partial_le hG (lo := lo) (hi := hi)
    (fun j => if E j then 0 else U j) (fun i y hy _ => by
      by_cases h : E i
      · rw [hpartE y i h]; simp [h]
      · rw [hpart y i h]
        simp only [h, if_false]
        refine hU _ (hφm y hy) (fun j hj => by simp [hφ, hj, hc]) i h) hx
  -- `φ` fixes `x` (its `E` coordinates are at the center) and the center
  have hφx : φ x = x := funext fun j => by
    by_cases h : E j
    · simp [hφ, h, hxE j h, hc]
    · simp [hφ, h]
  have hφc : φ (fun i => (lo i + hi i) / 2) = fun i => (lo i + hi i) / 2 := funext fun j => by
    by_cases h : E j <;> simp [hφ, hc]
  simp only [Function.comp, hφx, hφc] at this
  refine this.trans (le_of_eq ?_)
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : E j <;> simp [h]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
