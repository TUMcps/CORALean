module

public import CORALean.Global.BoxDiameter
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Applying a matrix cannot widen a box diameter past its operator norm

`d(box(M • S))` read coordinatewise is a row of `M` dotted against the spread
`x - y` of two points of `S`, so each coordinate is bounded by that row's
1-norm times `‖boxDiameter S‖`, and the largest row is `‖M‖` at the `l∞`
operator norm. Used to carry a `boxDiameter` bound through `e^{AΔt}`, the
linear step [1, Lemma 2]'s solver takes between abstraction errors.

The four `Matrix.linftyOp*` instances are picked locally, as every file here
that needs a matrix norm must.

## Inputs
* `M` – matrix
* `S` – set of vectors

## Hypotheses
* `hne` – the set is nonempty
* `hS` – the set is bounded

## Conclusion
* the image's box diameter is at most the matrix norm times the set's

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Applying `M` scales a box diameter by at most `M`'s own operator norm. -/
theorem boxDiameter_mulVec_image_le {M : Mat ℝ n n} {S : Set (Vec ℝ n)} (hne : S.Nonempty)
    (hS : Bornology.IsBounded S) :
    ‖boxDiameter ((M *ᵥ ·) '' S)‖ ≤ ‖M‖ * ‖boxDiameter S‖ := by -- --- PROOF ---
  -- bound the widest column-`i` gap between two points of `S`, then sandwich `sSup`/`sInf`
  have hcoord : ∀ i : Fin n, boxDiameter ((M *ᵥ ·) '' S) i ≤ ‖M‖ * ‖boxDiameter S‖ := by
    intro i
    have himg : (fun x : Vec ℝ n => x i) '' ((M *ᵥ ·) '' S)
        = (fun x : Vec ℝ n => (M *ᵥ x) i) '' S := by
      rw [Set.image_image]
    have hkey : ∀ x ∈ S, ∀ y ∈ S, (M *ᵥ x) i - (M *ᵥ y) i ≤ ‖M‖ * ‖boxDiameter S‖ := by
      intro x hx y hy
      -- `x - y` never exceeds `S`'s own diameter, and `M` scales it by at most `‖M‖`
      have hxy : ‖x - y‖ ≤ ‖boxDiameter S‖ := by
        rw [pi_norm_le_iff_of_nonneg (norm_nonneg (boxDiameter S))]
        intro j
        rw [Real.norm_eq_abs]
        exact (abs_sub_le_boxDiameter hS hx hy j).trans
          ((le_abs_self _).trans (norm_le_pi_norm (boxDiameter S) j))
      have hsub : (M *ᵥ x) i - (M *ᵥ y) i = (M *ᵥ (x - y)) i := by
        rw [Matrix.mulVec_sub]; rfl
      calc (M *ᵥ x) i - (M *ᵥ y) i = (M *ᵥ (x - y)) i := hsub
        _ ≤ |(M *ᵥ (x - y)) i| := le_abs_self _
        _ = ‖(M *ᵥ (x - y)) i‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖M *ᵥ (x - y)‖ := norm_le_pi_norm _ i
        _ ≤ ‖M‖ * ‖x - y‖ := Matrix.linfty_opNorm_mulVec M (x - y)
        _ ≤ ‖M‖ * ‖boxDiameter S‖ := mul_le_mul_of_nonneg_left hxy (norm_nonneg M)
    -- sandwich `sSup` between `sInf` and the bound `hkey` gives every pair
    have hsup : sSup ((fun x : Vec ℝ n => (M *ᵥ x) i) '' S)
        ≤ sInf ((fun x : Vec ℝ n => (M *ᵥ x) i) '' S) + ‖M‖ * ‖boxDiameter S‖ := by
      refine csSup_le (hne.image (fun x : Vec ℝ n => (M *ᵥ x) i)) ?_
      rintro _ ⟨x, hx, rfl⟩
      have h : (M *ᵥ x) i - ‖M‖ * ‖boxDiameter S‖
          ≤ sInf ((fun y : Vec ℝ n => (M *ᵥ y) i) '' S) := by
        refine le_csInf (hne.image (fun y : Vec ℝ n => (M *ᵥ y) i)) ?_
        rintro _ ⟨y, hy, rfl⟩
        linarith [hkey x hx y hy]
      linarith
    rw [boxDiameter, himg]; linarith
  -- `(M *ᵥ ·) '' S` is bounded, which is what `boxDiameter`'s own `sSup`/`sInf` need
  have hb : Bornology.IsBounded ((M *ᵥ ·) '' S) := by
    obtain ⟨C, hC⟩ := hS.exists_norm_le
    apply Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := (0 : Vec ℝ n))
      (r := ‖M‖ * C))
    rintro _ ⟨x, hx, rfl⟩
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (Matrix.linfty_opNorm_mulVec M x).trans (mul_le_mul_of_nonneg_left (hC x hx)
      (norm_nonneg M))
  -- and its box diameter is nonnegative, so its norm reads off each coordinate directly
  have hnn : ∀ i : Fin n, 0 ≤ boxDiameter ((M *ᵥ ·) '' S) i := fun i => by
    have h1 : sInf ((fun z : Vec ℝ n => z i) '' ((M *ᵥ ·) '' S))
        ≤ sSup ((fun z : Vec ℝ n => z i) '' ((M *ᵥ ·) '' S)) :=
      csInf_le_csSup ((hne.image (M *ᵥ ·)).image (fun z : Vec ℝ n => z i))
        (bddBelow_eval_image hb i) (bddAbove_eval_image hb i)
    rw [boxDiameter]; linarith
  rw [pi_norm_le_iff_of_nonneg (by positivity : (0:ℝ) ≤ ‖M‖ * ‖boxDiameter S‖)]
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (hnn i)]
  exact hcoord i

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
