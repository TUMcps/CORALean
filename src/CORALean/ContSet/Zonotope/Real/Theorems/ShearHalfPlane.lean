module

public import CORALean.ContSet.Zonotope.Real.Operations.Shear

@[expose] public section

/-!
# The shear keeps the generators in the upper half-plane

`(x, y) ↦ (x - κ y, y)` fixes `y`, and on `y = 0` it fixes `x`, so a generator in
`y > 0 ∨ (y = 0 ∧ x ≥ 0)` stays there. The sorted zonogons of [1, Alg. 3] are sheared without
leaving the hypotheses of the walk.

## Inputs
* `Z` – planar zonotope
* `κ` – shear factor
* `j` – generator index

## Hypotheses
* `hH` – generators point upward

## Conclusion
* sheared generators point upward

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". In Hybrid Systems: Computation and Control (HSCC), LNCS 4981,
      Springer, 2008, pp. 215-228.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.shear_half_plane (Z : Zonotope (Vec ℝ 2)) (κ : ℝ)
    (hH : ∀ j, 0 ≤ Z.G j 1 ∧ (0 < Z.G j 1 ∨ 0 ≤ Z.G j 0)) (j : Fin Z.h) : -- --- CONCL ---
    0 ≤ (Z.shear κ).G j 1 ∧ (0 < (Z.shear κ).G j 1 ∨ 0 ≤ (Z.shear κ).G j 0) := by -- --- PROOF ---
  obtain ⟨h0, h1⟩ := hH j
  refine ⟨h0, ?_⟩
  simp only [Zonotope.shear, Matrix.cons_val_zero, Matrix.cons_val_one]
  rcases h0.eq_or_lt with hy | hy
  · -- on the x-axis the shear is the identity
    right
    have hx : 0 ≤ Z.G j 0 := h1.resolve_left (by rw [← hy]; exact lt_irrefl 0)
    rw [← hy]
    linarith
  · exact Or.inl hy

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
