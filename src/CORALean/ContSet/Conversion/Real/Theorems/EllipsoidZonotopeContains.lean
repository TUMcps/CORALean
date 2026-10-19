module

public import CORALean.ContSet.Conversion.Real.Operations.Ellipsoid_to_Zonotope
public import CORALean.ContSet.Ellipsoid.Real.Theorems.MemConstructIff

@[expose] public section

/-!
# An ellipsoid as a zonotope

CORA's `'outer:box'`, `zonotope(q, sqrtm(Q))`: a point of the ellipsoid is `q + G u` with
`‖u‖₂ ≤ 1` (`mem_construct_iff`), so every coordinate of `u` lies in `[-1, 1]` and `u` is a
coefficient vector of the parallelotope on the columns of `G`.

CORA's `'inner:norm'` and `'outer:norm'` are [1, Thm. 2] and [1, Thm. 4]: points `S` on the unit
sphere, ideally spread evenly ([1, Lemma 4]), scaled by the inverse of a bound on the maximum,
or below the minimum, norm of `Z(S, 0)` and mapped by the ellipsoid's generator.
`zonotopeInnerNorm` and `zonotopeNorm` take `S` and the bound; the guarantees hold for any `S`.

## References

* [1] V. Gaßmann and M. Althoff. "Scalable Zonotope-Ellipsoid Conversions using the Euclidean
      Zonotope Norm". In Proc. of the 2020 American Control Conference (ACC), pp. 4715-4721,
      2020.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.zonotope_contains (E : Ellipsoid n) :
    E.construct ⊆ E.zonotope.construct := by -- --- PROOF ---
  intro x hx
  obtain ⟨u, hu, rfl⟩ := Ellipsoid.mem_construct_iff.mp hx
  -- `G *ᵥ u` is the sum of the columns weighted by `u`, each weight in `[-1, 1]`
  refine ⟨u, fun j => le_trans (abs_le_norm₂ u j) hu, ?_⟩
  congr 1
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, Ellipsoid.zonotope]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
