module

public import CORALean.ContSet.Zonotope.Real.Operations.MinnormPoint
public import CORALean.ContSet.Zonotope.Real.Theorems.HRepEq
public import CORALean.ContSet.Zonotope.Real.Theorems.FacetNormalDotSelfPos
public import CORALean.ContSet.Zonotope.Real.Theorems.MinnormOffsetMulSqrt
public import CORALean.ContSet.Zonotope.Real.Theorems.Basic

@[expose] public section

/-!
# `minnormPoint` is on the boundary

Stepping from the point further along the unit row of its facet leaves the zonotope: the facet's
inequality (the enclosing half of `hRep_eq` [1, Thm. 2]) is tight at the point. With
`minnormPoint_mem` this makes it a boundary point, and by `minnormPoint_dist` one at the
distance `minnorm Z`.

## Inputs
* `Z` – zonotope
* `S` – selected generator indices
* `t` – step length

## Hypotheses
* `hspan` – generators span the space
* `hC` – facet normal nonzero
* `ht` – step positive

## Conclusion
* stepping out along the normal leaves `Z`

## References

* [1] [M. Althoff. "On Computing the Minkowski Difference of Zonotopes". arXiv preprint
      arXiv:1512.02794,
      2015.](../../../../../../references/2015/althoff-arxiv-minkowski-difference.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.minnormPoint_not_mem_step (Z : Zonotope (Vec ℝ (n + 1)))
    (hspan : Submodule.span ℝ (Set.range Z.G) = ⊤) (S : Fin n → Fin Z.h)
    (hC : Z.facetNormal S ≠ 0) (t : ℝ) (ht : 0 < t) : -- --- CONCL ---
    Z.minnormPoint S +
      t • ((Real.sqrt (Z.facetNormal S ⬝ᵥ Z.facetNormal S))⁻¹ • Z.facetNormal S) ∉
      Z.construct := by -- --- PROOF ---
  -- the facet normal, its length, and the unit normal along which the step goes
  set C := Z.facetNormal S
  set r := Real.sqrt (C ⬝ᵥ C)
  set u := r⁻¹ • C with hu
  have hCC := Zonotope.facetNormal_dotProduct_self_pos Z S hC
  have hs : 0 < r := Real.sqrt_pos.mpr hCC
  have hss : r ^ 2 = C ⬝ᵥ C := Real.sq_sqrt hCC.le
  -- the facet inequality at the stepped point
  intro hmem
  rw [Zonotope.hRep_eq Z hspan] at hmem
  have h1 := hmem S
  unfold Zonotope.minnormPoint at h1
  have hdiff : Z.c + Z.minnormOffset S • u + t • u - Z.c = (Z.minnormOffset S + t) • u := by
    rw [add_smul]; abel
  rw [hdiff] at h1
  simp only [hu, dotProduct_smul, smul_eq_mul] at h1
  -- it reads `(b + t) ‖C‖ ≤ Δd = b ‖C‖`, which `t > 0` contradicts
  have heq : (Z.minnormOffset S + t) * (r⁻¹ * (C ⬝ᵥ C)) = (Z.minnormOffset S + t) * r := by
    field_simp
    rw [hss]
  have hnn := Zonotope.minnormOffset_nonneg Z S
  rw [heq, abs_of_nonneg (mul_nonneg (by linarith) hs.le),
    ← Zonotope.minnormOffset_mul_sqrt Z S hC] at h1
  nlinarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
