module

public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeZonotopeContains
public import CORALean.ContSet.Zonotope.Real.Operations.GenMap
public import CORALean.ContSet.ConZonotope.Real.ConZonotope
public import CORALean.ContSet.HPolytope.Real.Theorems.TranslateExact
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_ConZonotope
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains

@[expose] public section

/-!
# A halfspace description as a constrained zonotope

Exact, and the conversion that shows what constrained zonotopes are for: any
bounded halfspace description is one, with the rows kept rather than
approximated.

The generators come from a box enclosure — anything containing the polytope
would do — and the rows are then carried onto the coefficients by composing with
the generator map, after shifting by the centre. What the coefficients must
satisfy is exactly what the original rows said, so nothing is lost; the box is
only there to supply generators, and drops out.

This is the equivalence of polytopes and constrained zonotopes of
[1, Fig. 1 (Polytopes ↔ Constrained Zonotopes)].

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ} {P : HPolytope (Vec ℝ n)}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.conZonotope_exact
    (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) :
    (HPolytope.conZonotope up lo).construct = P.construct := by -- --- PROOF ---
  -- the coefficients' constraint says exactly that the point they name is in `P`
  have hmem : ∀ β : Vec ℝ (HPolytope.zonotope up lo).h,
      β ∈ ((P.translate (-(HPolytope.zonotope up lo).c)).comap
            (HPolytope.zonotope up lo).genMap).construct
        ↔ (HPolytope.zonotope up lo).c + (HPolytope.zonotope up lo).genMap β ∈ P.construct := by
    intro β
    rw [HPolytope.comap_exact, Set.mem_preimage, ← HPolytope.translate_exact]
    constructor
    · rintro ⟨y, hy, hxy⟩
      have h : (HPolytope.zonotope up lo).genMap β = -(HPolytope.zonotope up lo).c + y := hxy.symm
      rw [h]
      simpa using hy
    · intro h
      refine ⟨(HPolytope.zonotope up lo).c + (HPolytope.zonotope up lo).genMap β, h, ?_⟩
      show -(HPolytope.zonotope up lo).c
        + ((HPolytope.zonotope up lo).c + (HPolytope.zonotope up lo).genMap β) = _
      rw [neg_add_cancel_left]
  -- both directions off `hmem`, the enclosing zonotope supplying the coefficients
  ext x
  constructor
  · rintro ⟨β, -, hP, rfl⟩
    exact (hmem β).mp hP
  · intro hx
    obtain ⟨β, hβ, hxβ⟩ := HPolytope.zonotope_contains up lo hx
    refine ⟨β, hβ, (hmem β).mpr ?_, hxβ⟩
    show (HPolytope.zonotope up lo).c + ∑ j, β j • (HPolytope.zonotope up lo).G j ∈ P.construct
    rwa [← hxβ]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
