module

public import CORALean.ContSet.Capsule.Real.Theorems.ConstructEqEmpty
public import CORALean.ContSet.Capsule.Real.Theorems.ConstructEqAdd
public import Mathlib.Analysis.Convex.Mul

@[expose] public section

/-!
# A capsule is convex

Avoids Minkowski's inequality entirely. At `C.r < 0` the set is `∅`. Otherwise
`construct_eq_add` writes `C.construct` as the *sum* of two convex sets: the
segment `{c + t g | t ∈ [-1, 1]}`, an affine image of `Icc`, and the ball `{y |
∑ y i ^ 2 ≤ r ^ 2}`, whose defining function is a finite sum of even powers of
linear functionals and so convex — no norm needed for either part.

## Inputs
* `C` – capsule

## Hypotheses
* none

## Conclusion
* `C` is convex
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A finite sum of even powers of linear functionals, so convex on all of `Vec ℝ n`. -/
theorem aux_convexOn_sumSq : -- --- CONCL ---
    ConvexOn ℝ (Set.univ : Set (Vec ℝ n)) (fun y => ∑ i, y i ^ 2) := by -- --- PROOF ---
  have heq : (fun y : Vec ℝ n => ∑ i, y i ^ 2) = ∑ i : Fin n, fun y : Vec ℝ n => y i ^ 2 :=
    (Finset.sum_fn Finset.univ (fun (i : Fin n) (y : Vec ℝ n) => y i ^ 2)).symm
  rw [heq]
  refine Finset.sum_induction _ (ConvexOn ℝ (Set.univ : Set (Vec ℝ n)))
    (fun _ _ hf hg => hf.add hg) (convexOn_const 0 convex_univ) fun i _ =>
    (even_two.convexOn_pow (𝕜 := ℝ)).comp_linearMap (LinearMap.proj i : Vec ℝ n →ₗ[ℝ] ℝ)


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.convex_construct (C : Capsule n) : -- --- CONCL ---
    Convex ℝ C.construct := by -- --- PROOF ---
  rcases lt_or_ge C.r 0 with hr | hr
  · rw [Capsule.construct_eq_empty hr]
    exact convex_empty
  · have hball : Convex ℝ {y : Vec ℝ n | ∑ i, y i ^ 2 ≤ C.r ^ 2} := by
      simpa [Set.sep_univ] using aux_convexOn_sumSq.convex_le (C.r ^ 2)
    have hseg : Convex ℝ ((fun t : ℝ => C.c + t • C.g) '' Set.Icc (-1 : ℝ) 1) := by
      have heq : (fun t : ℝ => C.c + t • C.g) '' Set.Icc (-1 : ℝ) 1
          = (fun x => C.c + x) ''
              (LinearMap.toSpanSingleton ℝ (Vec ℝ n) C.g '' Set.Icc (-1 : ℝ) 1) := by
        simp only [Set.image_image, LinearMap.toSpanSingleton_apply]
      rw [heq]
      exact ((convex_Icc (-1 : ℝ) 1).linear_image
        (LinearMap.toSpanSingleton ℝ (Vec ℝ n) C.g)).translate C.c
    rw [Capsule.construct_eq_add hr]
    exact hseg.add hball

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
