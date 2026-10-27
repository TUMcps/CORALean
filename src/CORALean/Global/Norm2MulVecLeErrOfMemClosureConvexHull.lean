module

public import CORALean.Global.Err
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

/-!
# `err` sees a set and its closed convex hull alike

[1, Prop. 11]'s `err(S) = rad(box(S))` reads only the extreme values of each coordinate over `S`,
and a closed convex hull has the same extreme values: `inf_i S ≤ y_i ≤ sup_i S` cuts out a closed
convex slab that holds `S`, so it holds the hull. For a matrix `M`, every `y` in the closed convex
hull of `T` then has `‖My‖₂ ≤ err(MT)`. This is how an error bound stated with `err` survives an
enclosure that only holds up to convex combination, as in [1, Prop. 3] and [1, Prop. 11].

## Inputs
* `M` – matrix
* `T` – bounded set
* `y` – point of the closed convex hull

## Hypotheses
* `hT` – the set is bounded
* `hy` – the point lies in the closed convex hull of the set

## Conclusion
* the Euclidean norm of the matrix image is at most the radius of the image set

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, 2023.](../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `‖My‖₂ ≤ err(MT)` for every `y` in the closed convex hull of a bounded `T`. -/
theorem norm₂_mulVec_le_err_of_mem_closure_convexHull (M : Mat ℝ n n) {T : Set (Vec ℝ n)}
    (hT : Bornology.IsBounded T) {y : Vec ℝ n}
    (hy : y ∈ closure (convexHull ℝ T)) : -- --- CONCL ---
    ‖M *ᵥ y‖₂ ≤ err ((fun x => M *ᵥ x) '' T) := by -- --- PROOF ---
  set L := LinearMap.toContinuousLinearMap (Matrix.mulVecLin M) with hL
  set I := (fun x => M *ᵥ x) '' T with hI
  have hIb : Bornology.IsBounded I := L.lipschitz.isBounded_image hT
  set lo : Fin n → ℝ := fun i => sInf ((fun z : Vec ℝ n => z i) '' I) with hlo
  set hi : Fin n → ℝ := fun i => sSup ((fun z : Vec ℝ n => z i) '' I) with hhi
  -- the slab of every coordinate is closed, convex and holds `T`
  set K := {z : Vec ℝ n | ∀ i, lo i ≤ (M *ᵥ z) i ∧ (M *ᵥ z) i ≤ hi i} with hK
  -- each coordinate of `M z` is continuous in `z`
  have hcoord : ∀ i, Continuous fun z : Vec ℝ n => (M *ᵥ z) i := fun i =>
    (continuous_apply i).comp L.continuous
  have hKc : IsClosed K := by
    simp only [hK, Set.setOf_forall]
    exact isClosed_iInter fun i => (isClosed_le continuous_const (hcoord i)).inter
      (isClosed_le (hcoord i) continuous_const)
  -- a convex combination of two points of the slab stays in it
  have hKv : Convex ℝ K := by
    intro a ha b hb θ φ hθ hφ hθφ i
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    obtain ⟨ha1, ha2⟩ := ha i
    obtain ⟨hb1, hb2⟩ := hb i
    have el : lo i = θ * lo i + φ * lo i := by rw [← add_mul, hθφ, one_mul]
    have eh : hi i = θ * hi i + φ * hi i := by rw [← add_mul, hθφ, one_mul]
    have h1 := mul_le_mul_of_nonneg_left ha1 hθ
    have h2 := mul_le_mul_of_nonneg_left hb1 hφ
    have h3 := mul_le_mul_of_nonneg_left ha2 hθ
    have h4 := mul_le_mul_of_nonneg_left hb2 hφ
    constructor <;> linarith
  have hTK : T ⊆ K := fun z hz i =>
    ⟨csInf_le (bddBelow_eval_image hIb i) ⟨M *ᵥ z, ⟨z, hz, rfl⟩, rfl⟩,
      le_csSup (bddAbove_eval_image hIb i) ⟨M *ᵥ z, ⟨z, hz, rfl⟩, rfl⟩⟩
  have hyK : y ∈ K := closure_minimal (convexHull_min hTK hKv) hKc hy
  -- coordinatewise under the extreme magnitudes, so under their Euclidean norm
  show ‖M *ᵥ y‖₂ ≤ ‖fun i => max |hi i| |lo i|‖₂
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  obtain ⟨h1, h2⟩ := hyK i
  have hab : |(M *ᵥ y) i| ≤ max |hi i| |lo i| :=
    abs_le.mpr ⟨by linarith [neg_abs_le (lo i), le_max_right |hi i| |lo i|],
      h2.trans ((le_abs_self (hi i)).trans (le_max_left _ _))⟩
  rw [← sq_abs ((M *ᵥ y) i)]
  exact pow_le_pow_left₀ (abs_nonneg _) hab 2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
