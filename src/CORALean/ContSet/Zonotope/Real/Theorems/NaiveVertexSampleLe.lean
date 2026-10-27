module

public import CORALean.ContSet.Zonotope.Real.Theorems.IsGreatestCoeffNormCorner
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope

@[expose] public section

/-!
# Naive vertex sampling under-approximates

`[1, Eq. 10]`: sampling sign vectors `a₁, …, a_N` and taking
`r_vs = maxᵢ ‖G aᵢ + c - d‖_{E_q(H)}` gives `r_vs ≤ r(Ẑ, Ê)`: every sampled corner is a point
of the zonotope. Whatever the samples, random or not; `r` is the maximum of
`[1, Sec. III]`.

## Inputs
* `Z` – zonotope
* `H` – linear map
* `d` – offset
* `r` – greatest coefficient norm
* `a` – sampled corner signs

## Hypotheses
* `hr` – `r` is the greatest norm over `Z`
* `hN` – at least one sample

## Conclusion
* the sampled norm is at most `r`

## References

* [1] [A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the Zonotope
      and Ellipsotope Containment Problems". 2024 European Control Conference (ECC),
      2024.](../../../../../../references/2024/kulmburg-ecc-zonotope-ellipsotope-containment.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n N : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.naive_vertex_sample_le (Z : Zonotope (Vec ℝ n)) (H : E →ₗ[ℝ] Vec ℝ n)
    (d : Vec ℝ n) {r : ℝ} (hr : IsGreatest ((fun p => coeffNorm H (p - d)) '' Z.construct) r)
    (a : Fin N → Fin Z.h → Bool) (hN : (Finset.univ : Finset (Fin N)).Nonempty) :
    Finset.univ.sup' hN (fun i => coeffNorm H (Z.corner (a i) - d)) ≤ r := by
  refine Finset.sup'_le hN _ fun i _ => hr.2 ⟨Z.corner (a i), ?_, rfl⟩
  -- a corner is a point of the zonotope
  rw [Z.construct_eq_convexHull_corner]
  exact subset_convexHull ℝ _ ⟨a i, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
