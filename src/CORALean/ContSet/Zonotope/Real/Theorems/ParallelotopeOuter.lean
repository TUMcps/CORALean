module

public import CORALean.ContSet.Zonotope.Real.Operations.Parallelotope
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# The parallelotope `Γ box(Γ⁻¹Z)` encloses `Z`

[1, Prop. 8], following its sketch of proof: `Γ⁻¹` maps `Z` into `Γ⁻¹Z`, which its box
holds, `Zonotope.interval_contains`; `Γ` maps the box back, and `Γ Γ⁻¹ = I` returns every
point of `Z` to itself. The rank of `Γ` is spent there and nowhere else.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Computing Reachable Sets of Hybrid
      Systems Using a Combination of Zonotopes and Polytopes". Nonlinear
      Analysis: Hybrid Systems, 4(2):233-249, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 8]: at a full-rank `Γ`, `Z ⊆ Γ box(Γ⁻¹Z)`. -/
theorem Zonotope.parallelotope_outer {Γ : Mat ℝ n n} (hΓ : IsUnit Γ.det)
    (Z : Zonotope (Vec ℝ n)) : Z.construct ⊆ (Z.parallelotope Γ).construct := by -- --- PROOF ---
  intro x hx
  -- `Γ⁻¹ x` lies in `Γ⁻¹Z`, hence in its box
  have hZ' : Γ⁻¹ *ᵥ x ∈ (Zonotope.mtimes Γ⁻¹ Z).construct := by
    rw [← Zonotope.mtimes_exact]; exact ⟨x, hx, rfl⟩
  have hbox := Interval.zonotope_contains _ (Zonotope.interval_contains _ hZ')
  -- and `Γ` maps it back to `x`
  rw [Zonotope.parallelotope, ← Zonotope.mtimes_exact]
  refine ⟨_, hbox, ?_⟩
  show Γ *ᵥ (Γ⁻¹ *ᵥ x) = x
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hΓ, Matrix.one_mulVec]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
