module

public import CORALean.NN.Operations.CatMaxSegments
public import CORALean.NN.Theorems.CatEvalAffineIff
public import CORALean.NN.Theorems.CatEvalCompIff
public import CORALean.NN.Layers.Theorems.SelectMatMulVecAddZero
public import CORALean.NN.Theorems.CatMaxSegmentEvalIff

@[expose] public section

/-!
# Pooling a row of windows, one CAT step at a time

[1, Sec. II (MaxPool to CAT)]: after `a` pooled coordinates, `r` windows of `k + 1` are each
replaced by their maximum, window `j - a` read at `a + (k + 1) (j - a), …`, and the chain maps a
point to nothing else. By induction on `r`: the first window is `Cat.maxSegment`'s, after which
window `j - a` of the rest sits `k` coordinates further left, the first window's `k + 1`
having become one; the identity maps framing a step only rename.

## Inputs
* `k` – window size minus one

## Hypotheses
* none

## Conclusion
* the row of steps maps a point to the output iff the output holds the window maxima

## References

* [1] T. Gehr, M. Mirman, D. Drachsler-Cohen, P. Tsankov, S. Chaudhuri and M. Vechev. "AI2:
      Safety and Robustness Certification of Neural Networks with Abstract Interpretation".
      IEEE S&P 2018, pp. 3-18.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Window `j - a` lies inside the `r` windows. -/
theorem aux_lt_of_window {a k r j q : ℕ} (hj : j < a + r) (ha : a ≤ j) (hq : q < k + 1) :
    a + (k + 1) * (j - a) + q < a + (k + 1) * r := by
  have : (k + 1) * (j - a) + (k + 1) ≤ (k + 1) * r := by
    rw [← Nat.mul_succ]
    exact Nat.mul_le_mul_left _ (by omega)
  omega


-- =======================================  MAIN THEOREM  ======================================= --

theorem Cat.maxSegments_eval_iff (k : ℕ) : -- --- CONCL ---
    ∀ (a r : ℕ) (x : Vec ℝ (a + (k + 1) * r))
    (y : Vec ℝ (a + r)),
    -- the pooled coordinates, then the maximum of each window
    let yv : Vec ℝ (a + r) := fun j => if _h : j.val < a then x ⟨j.val, by omega⟩
      else Real.windowMax fun q : Fin (k + 1) =>
        x ⟨a + (k + 1) * (j.val - a) + q.val, aux_lt_of_window j.isLt (by omega) q.isLt⟩
    (Cat.maxSegments (𝕋 := 𝕋) k a r).Evaluates x y ↔ y = yv := by -- --- PROOF ---
  intro a r
  induction r generalizing a with
  | zero =>
    intro x y yv
    simp only [Cat.maxSegments]
    rw [Cat.eval_affine_iff]
    -- every coordinate is among the `a` already pooled
    have h : (toRealMat (selectMat (𝕋 := 𝕋) fun i : Fin (a + 0) =>
          (⟨i.val, by simp⟩ : Fin (a + (k + 1) * 0))) *ᵥ x
        + toRealVec (fun _ => (zero : 𝕋))) = yv := by
      funext j
      simp only [yv]
      rw [selectMat_mulVec_add_zero, dif_pos (by simp)]
    rw [h]
  | succ r ih =>
    intro x y yv
    simp only [Cat.maxSegments]
    -- the chain has a value: split, the first window, the rest, renamed; and only that one
    have key : (∃ y, (Cat.comp (.affine (selectMat fun i : Fin (a + (r + 1)) =>
          (⟨i.val, by have := i.isLt; omega⟩ : Fin (a + 1 + r))) fun _ => (zero : 𝕋))
        (.comp (Cat.maxSegments k (a + 1) r) (.comp (Cat.maxSegment a k ((k + 1) * r))
          (.affine (selectMat fun i : Fin (a + (k + 1) + (k + 1) * r) =>
            (⟨i.val, by have := i.isLt; rw [Nat.mul_succ]; omega⟩ :
              Fin (a + (k + 1) * (r + 1)))) fun _ => zero)))).Evaluates x y) ∧
        -- and every value is the one the statement names
        ∀ y, (Cat.comp (.affine (selectMat fun i : Fin (a + (r + 1)) =>
          (⟨i.val, by have := i.isLt; omega⟩ : Fin (a + 1 + r))) fun _ => (zero : 𝕋))
        (.comp (Cat.maxSegments k (a + 1) r) (.comp (Cat.maxSegment a k ((k + 1) * r))
          (.affine (selectMat fun i : Fin (a + (k + 1) + (k + 1) * r) =>
            (⟨i.val, by have := i.isLt; rw [Nat.mul_succ]; omega⟩ :
              Fin (a + (k + 1) * (r + 1)))) fun _ => zero)))).Evaluates x y →
        y = yv := by
      refine ⟨⟨_, Cat.Evaluates.comp _ _ _ (Cat.Evaluates.comp _ _ _ (Cat.Evaluates.comp _ _ _
        (Cat.Evaluates.affine _ _ x) ((Cat.maxSegment_eval_iff _ _ _ _ _).mpr rfl))
        ((ih _ _ _).mpr rfl)) (Cat.Evaluates.affine _ _ _)⟩, fun y hy => ?_⟩
      -- peel the four maps off, each a function of its input
      obtain ⟨z₃, hz₃, hy⟩ := (Cat.eval_comp_iff _ _ _ _).mp hy
      obtain ⟨z₂, hz₂, hz₃⟩ := (Cat.eval_comp_iff _ _ _ _).mp hz₃
      obtain ⟨z₁, hz₁, hz₂⟩ := (Cat.eval_comp_iff _ _ _ _).mp hz₂
      rw [Cat.eval_affine_iff] at hz₁ hy
      rw [Cat.maxSegment_eval_iff] at hz₂
      replace hz₃ := (ih _ _ _).mp hz₃
      subst hz₁ hz₂ hz₃ hy
      funext j
      simp only [yv]
      rw [selectMat_mulVec_add_zero]
      -- an already pooled coordinate is kept
      by_cases h1 : j.val < a
      · simp [h1, Nat.lt_succ_of_lt h1, selectMat_mulVec, toRealVec, toReal_zero]
      by_cases h2 : j.val = a
      · -- the first window
        simp only [h2, dite_false, lt_add_iff_pos_right, dite_true, lt_irrefl, if_true,
          Nat.lt_succ_self]
        simp [selectMat_mulVec, toRealVec, toReal_zero]
      · -- a later window, `k` coordinates further left in the rest
        have h3 : ¬ j.val < a + 1 := by omega
        have hidx : ∀ q : Fin (k + 1),
            a + 1 + (k + 1) * (j.val - (a + 1)) + q.val + k
              = a + (k + 1) * (j.val - a) + q.val := by
          intro q
          have : j.val - a = (j.val - (a + 1)) + 1 := by omega
          rw [this, Nat.mul_succ]
          omega
        -- its coordinates lie past the first window, which `fᵢ` shifted by `k`
        have hge : ∀ q : Fin (k + 1), ¬ a + 1 + (k + 1) * (j.val - (a + 1)) + q.val < a := by
          intro q; omega
        have hne : ∀ q : Fin (k + 1), a + 1 + (k + 1) * (j.val - (a + 1)) + q.val ≠ a := by
          intro q; omega
        simp only [h1, h3, dite_false, hge, hne, if_false]
        simp [hidx, selectMat_mulVec, toRealVec, toReal_zero]
    -- a value exists, and every value is that one
    constructor
    · exact key.2 y
    · rintro rfl
      obtain ⟨y', hy'⟩ := key.1
      rw [← key.2 y' hy']
      exact hy'

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
