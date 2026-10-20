module

public import CORALean.ContSet.LevelSet.Real.LevelSet
public import CORALean.ContSet.PolyZonotope.Real.Theorems.IsCompact

@[expose] public section

/-!
# A level set that is no polynomial zonotope

A polynomial zonotope is a level set (`LevelSet.exists_construct_eq`), and the inclusion is strict:
a polynomial zonotope is compact, and the half-line `{x | 0 ≤ x₀}` is a level set that is not.

This is the arrow from polynomial zonotopes to level sets of
[1, Fig. 1 (Polynomial Zonotopes → Level Sets)].

## Inputs
* none

## Hypotheses
* none

## Conclusion
* some level set on the line is no polynomial zonotope

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.

-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem LevelSet.exists_not_polyZonotope : -- --- CONCL ---
    ∃ L : LevelSet 1,
      ¬ ∃ pZ : PolyZonotope (Vec ℝ 1), pZ.construct = L.construct := by -- --- PROOF ---
  refine ⟨⟨1, fun x _ => -x 0, fun _ => .le⟩, ?_⟩
  rintro ⟨pZ, hpZ⟩
  -- a compact set is bounded, and the half-line has points of every norm
  obtain ⟨C, hC⟩ := (isBounded_iff_forall_norm_le.mp pZ.isCompact_construct.isBounded)
  have hmem : (fun _ => |C| + 1 : Vec ℝ 1) ∈ pZ.construct := by
    rw [hpZ]
    intro i
    simp only [CompOp.holds, neg_nonpos]
    exact (abs_nonneg C).trans (le_add_of_nonneg_right zero_le_one)
  have h := hC _ hmem
  have h0 : ‖(fun _ => |C| + 1 : Vec ℝ 1) 0‖ ≤ ‖(fun _ => |C| + 1 : Vec ℝ 1)‖ :=
    norm_le_pi_norm (fun _ => |C| + 1 : Vec ℝ 1) 0
  rw [Real.norm_of_nonneg (by positivity)] at h0
  linarith [le_abs_self C]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
