module

public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# `ConZonotope.rowBound`

[1, Alg. 1]'s eq. 12, before intersecting with `[-1,1]`: row `i` of `Aξ = b` solved for
coefficient `j`, `a_ij⁻¹bᵢ − a_ij⁻¹Σ_{k≠j}a_ik Eₖ`, as the two endpoints of `Rⱼ`
(whichever way the sign of `a_ij` swaps them). `tightenCoeff` is where this meets the
running box, and `tighten_outer` is why it is sound to.

## Inputs
* `nc` – number of constraints
* `ng` – number of generators
* `A` – constraint matrix
* `b` – constraint offset
* `i` – constraint row
* `j` – coefficient to bound
* `E` – current coefficient box

## Output
* the interval row i allows for coefficient j

## References

* [1] V. Raghuraman and J. P. Koeln. "Set operations and order reductions for
      constrained zonotopes". Automatica, 139:110204, 2022. arXiv:2009.06039.
-/

-- Authors:       Claude Opus 5
-- Written:       21-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Eq. (12)'s two endpoints for `Rⱼ`, from row `i` of `Aξ = b`. -/
noncomputable def ConZonotope.rowBound {nc ng : ℕ} (A : Mat ℝ nc ng) (b : Vec ℝ nc)
    (i : Fin nc) (j : Fin ng) (E : Interval (Vec ℝ ng)) : Interval ℝ :=
  let Slo := ∑ k ∈ Finset.univ.erase j, min (A i k * E.inf k) (A i k * E.sup k)
  let Shi := ∑ k ∈ Finset.univ.erase j, max (A i k * E.inf k) (A i k * E.sup k)
                                          -- Σ_{k≠j} a_ik Ek, bounded entrywise
  ⟨(b i - Shi) / A i j, (b i - Slo) / A i j⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
