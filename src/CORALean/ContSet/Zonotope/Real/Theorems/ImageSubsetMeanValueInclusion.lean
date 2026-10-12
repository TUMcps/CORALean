import CORALean.ContSet.Zonotope.Real.Operations.MeanValueInclusion
import CORALean.ContSet.Zonotope.Real.Theorems.InclusionOuter
import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The mean-value inclusion function encloses the image of a zonotope

[1, Thm. 5]: for `f(x, w)`, a zonotope `X = p ⊕ H Bᵐ`, a set `W`, a box `I ⊇ f(p, W)` and an
interval matrix `[M] ∋ ∇ₓf(ξ, w) H` for every `ξ ∈ X`, `w ∈ W`, then `f(X, W) ⊆ Ψ(X, W)`. The
paper's proof is the mean value extension: `f(x, w) ∈ f(p, w) ⊕ ∇ₓf(X, w) H Bᵐ`. Here it is the
mean value theorem on each coordinate along the segment from `p` to `x`, which lies in `X`: the
points `ξᵢ` differ by row, and an interval matrix is entrywise, so the rows assemble into one `M ∈
[M]`. `f` is differentiable in `x`, as the mean value theorem needs ([1, Thm. 3]).

## References

* [1] T. Alamo, J. M. Bravo and E. F. Camacho. "Guaranteed state estimation by zonotopes".
      Automatica, 41(6):1035-1043, 2005.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.image_subset_meanValueInclusion {n nw : ℕ}
    (f : Vec ℝ n → Vec ℝ nw → Vec ℝ n) (W : Set (Vec ℝ nw)) (X : Zonotope (Vec ℝ n))
    (I : Interval (Vec ℝ n)) (IM : Interval (Mat ℝ n X.h))
    (hdiff : ∀ w ∈ W, Differentiable ℝ fun x => f x w)
    (hI : ∀ w ∈ W, f X.c w ∈ I.construct)
    (hM : ∀ x ∈ X.construct, ∀ w ∈ W,
      (Matrix.of fun i j => fderiv ℝ (fun x => f x w) x (X.G j) i : Mat ℝ n X.h) ∈ IM.construct) :
    ∀ x ∈ X.construct, ∀ w ∈ W, f x w ∈
      (Zonotope.meanValueInclusion I IM).construct := by -- --- PROOF ---
  intro x hx w hw
  obtain ⟨β, hβ, rfl⟩ := hx
  set d : Vec ℝ n := ∑ j, β j • X.G j with hd
  -- the mean value theorem on coordinate `i`, along the segment from the centre to `x`
  have key : ∀ i, ∃ ξ ∈ X.construct,
      f (X.c + d) w i - f X.c w i = fderiv ℝ (fun x => f x w) ξ d i := by
    intro i
    have hder : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f (X.c + t • d) w i)
        (fderiv ℝ (fun x => f x w) (X.c + t • d) d i) t := by
      intro t
      have h1 : HasDerivAt (fun t : ℝ => X.c + t • d) d t := by
        simpa using ((hasDerivAt_id t).smul_const d).const_add X.c
      exact hasDerivAt_pi.mp ((hdiff w hw (X.c + t • d)).hasFDerivAt.comp_hasDerivAt t h1) i
    obtain ⟨t, ⟨ht0, ht1⟩, ht⟩ := exists_hasDerivAt_eq_slope
      (fun t : ℝ => f (X.c + t • d) w i) (fun t => fderiv ℝ (fun x => f x w) (X.c + t • d) d i)
      zero_lt_one (fun t _ => (hder t).continuousAt.continuousWithinAt) (fun t _ => hder t)
    refine ⟨X.c + t • d, ⟨fun j => t * β j, fun j => ?_, ?_⟩, ?_⟩
    · -- the segment stays in the zonotope: its coefficients shrink by `t`
      rw [abs_mul, abs_of_pos ht0]
      nlinarith [hβ j, abs_nonneg (β j)]
    · simp [hd, Finset.smul_sum, mul_smul]
    · simpa using ht.symm
  choose ξ hξ hEq using key
  -- one matrix from the rows `∇ₓf(ξᵢ, w) H`
  set M : Mat ℝ n X.h := Matrix.of fun i j => fderiv ℝ (fun x => f x w) (ξ i) (X.G j) i with hMdef
  have hMmem : M ∈ IM.construct := fun idx => hM (ξ idx.1) (hξ idx.1) w hw idx
  have hfx : f (X.c + d) w = (M *ᵥ β) + f X.c w := by
    ext i
    have h1 : f (X.c + d) w i = f X.c w i + fderiv ℝ (fun x => f x w) (ξ i) d i := by
      linarith [hEq i]
    rw [Pi.add_apply, h1, add_comm]
    congr 1
    simp [hMdef, hd, Matrix.mulVec, dotProduct, map_sum, map_smul, Finset.sum_apply, mul_comm]
  -- the first term is in the inclusion of the interval matrix, the second in the box
  rw [Zonotope.meanValueInclusion, ← Zonotope.plus_exact]
  refine ⟨M *ᵥ β, ?_, f X.c w, Interval.zonotope_contains I (hI w hw), ?_⟩
  · exact Zonotope.inclusion_outer 0 IM (by
      simp only [Set.mem_iUnion]
      exact ⟨M, hMmem, β, hβ, by simp⟩)
  · simp [hfx]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
