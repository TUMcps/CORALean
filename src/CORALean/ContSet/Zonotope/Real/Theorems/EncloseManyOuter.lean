module

public import CORALean.ContSet.Zonotope.Real.Operations.EncloseMany
public import CORALean.ContSet.Zonotope.Real.Theorems.EncloseManyBasisIsUnit
public import CORALean.ContSet.Zonotope.Real.Theorems.ReduceGirardOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# `encloseMany` encloses every cell

Outer, not exact: each cell is first reduced to a parallelotope containing it, then boxed in the
rotated frame. The rotation is invertible for a nonzero direction (`encloseManyBasis_isUnit`),
so the round trip `R · R⁻¹` returns each point.

Source: [1].

## References

* [1] `contSet/@zonotope/encloseMany.m`, CORA (Sep. 2025).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {m q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.encloseMany_outer (Zs : Fin (q + 1) → Zonotope (Vec ℝ (m + 1)))
    (direction : Vec ℝ (m + 1)) (hd : direction ≠ 0) (i : Fin (q + 1)) :
    (Zs i).construct ⊆ (Zonotope.encloseMany Zs direction).construct := by -- --- PROOF ---
  intro x hx
  have hunit := Zonotope.encloseManyBasis_isUnit direction hd
  have hdet : IsUnit (Zonotope.encloseManyBasis direction).det := hunit
  -- the cell, its parallelotope, and the rotated parallelotope
  have h1 : x ∈ ((Zs i).reduceGirard 1).construct := Zonotope.reduceGirard_outer _ _ hx
  have h2 : (Zonotope.encloseManyBasis direction)⁻¹ *ᵥ x ∈
      (Zonotope.mtimes (Zonotope.encloseManyBasis direction)⁻¹
        ((Zs i).reduceGirard 1)).construct := by
    rw [← Zonotope.mtimes_exact]
    exact ⟨x, h1, rfl⟩
  -- its interval hull, then the hull over all cells
  have h3 := Zonotope.interval_contains _ h2
  unfold Zonotope.encloseMany
  simp only
  rw [← Zonotope.mtimes_exact]
  refine ⟨(Zonotope.encloseManyBasis direction)⁻¹ *ᵥ x, Interval.zonotope_contains _ ?_, ?_⟩
  · intro k
    refine ⟨?_, ?_⟩
    · exact Finset.inf'_le_of_le _ (Finset.mem_univ i) ((h3 k).1)
    · exact Finset.le_sup'_of_le _ (Finset.mem_univ i) ((h3 k).2)
  · show _ *ᵥ (_ *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
