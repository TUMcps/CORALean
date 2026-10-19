module

public import CORALean.ContDynamics.NonlinearSys.Operations.VarInputs
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MapExact
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.PolyZonotope.Real.Theorems.PlusExact
public import CORALean.ContSet.PolyZonotope.Real.Theorems.QuadBilinApply
public import CORALean.ContSet.PolyZonotope.Real.Theorems.QuadMapExact
public import CORALean.ContSet.PolyZonotope.Real.Theorems.QuadMapMixedExact
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

@[expose] public section

/-!
# `varInputs` holds every value the varying input part can take

`[1, Eq. 7]` read as a membership: at any `z`, `z∆` and `u∆` drawn from the three
sets, the second-order part of `v∆` lies in `varInputs` at those sets. The
statement is in the coordinates `[1]` writes them in, `D i j k` being the second
derivative and the bracket the double sum over `j` and `k`.

Its three hypotheses are three separate memberships, which is what makes the
theorem cover both readings of `[1, Eq. 7]`: the paper quantifies `z` over
`R(τs) × U` there and over `R(ts) × U` in Sec. 4.2, and either is an instance.

The proof is one exactness fact per piece — `mtimes`, `map`, `plus` three times,
`quadMapMixed` twice and `quadMap` once — after the double sum has been read back
as the three pairings. Only `plus` loses anything, and it loses it by letting the
three terms choose separately; every other step is an equality.

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
      Polynomialization and Non-Convex Sets". HSCC 2013.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

open Matrix Pointwise

variable {n m o : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every value `[1, Eq. 7]` admits lies in `varInputs` at the same three sets. -/
theorem varInputs_outer (B : Mat ℝ n m) (D : Fin n → Mat ℝ o o)
    {Rz RzΔ : PolyZonotope (Vec ℝ o)} {UΔ : PolyZonotope (Vec ℝ m)} {z zΔ : Vec ℝ o}
    {uΔ : Vec ℝ m} (hz : z ∈ Rz.construct) (hzΔ : zΔ ∈ RzΔ.construct)
    (huΔ : uΔ ∈ UΔ.construct) : -- --- CONCL ---
    (fun i => (B *ᵥ uΔ) i
        + (2 : ℝ)⁻¹ * ∑ j, ∑ k, D i j k * (z j * zΔ k + zΔ j * z k + zΔ j * zΔ k))
      ∈ (varInputs B D Rz RzΔ UΔ).construct := by -- --- PROOF ---
  -- the paper's double sum is the three pairings, distributed and split
  have hsum : ∀ i, ∑ j, ∑ k, D i j k * (z j * zΔ k + zΔ j * z k + zΔ j * zΔ k)
      = PolyZonotope.quadBilin D z zΔ i + PolyZonotope.quadBilin D zΔ z i
        + PolyZonotope.quadBilin D zΔ zΔ i := by
    intro i
    rw [PolyZonotope.quadBilin_apply, PolyZonotope.quadBilin_apply, PolyZonotope.quadBilin_apply]
    simp only [mul_add, Finset.sum_add_distrib]
  have hval : (fun i => (B *ᵥ uΔ) i
        + (2 : ℝ)⁻¹ * ∑ j, ∑ k, D i j k * (z j * zΔ k + zΔ j * z k + zΔ j * zΔ k))
      = B *ᵥ uΔ + ((2 : ℝ)⁻¹ • (LinearMap.id : Vec ℝ n →ₗ[ℝ] Vec ℝ n))
          (PolyZonotope.quadBilin D z zΔ + PolyZonotope.quadBilin D zΔ z
            + PolyZonotope.quadBilin D zΔ zΔ) := by
    funext i
    simp only [Pi.add_apply, LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [hsum i]
  -- and then one exactness fact per piece, the sums read the other way round
  rw [hval, varInputs, ← PolyZonotope.plus_exact]
  refine Set.add_mem_add ?_ ?_
  · rw [← PolyZonotope.mtimes_exact]
    exact ⟨uΔ, huΔ, rfl⟩
  · rw [← PolyZonotope.map_exact]
    refine ⟨_, ?_, rfl⟩
    rw [← PolyZonotope.plus_exact, ← PolyZonotope.plus_exact]
    refine Set.add_mem_add (Set.add_mem_add ?_ ?_) ?_
    · rw [← PolyZonotope.quadMapMixed_exact]
      exact ⟨(z, zΔ), ⟨hz, hzΔ⟩, rfl⟩
    · rw [← PolyZonotope.quadMapMixed_exact]
      exact ⟨(zΔ, z), ⟨hzΔ, hz⟩, rfl⟩
    · rw [← PolyZonotope.quadMap_exact]
      exact ⟨zΔ, hzΔ, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
