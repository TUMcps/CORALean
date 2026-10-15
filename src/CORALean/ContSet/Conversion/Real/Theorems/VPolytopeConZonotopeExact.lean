module

public import CORALean.ContSet.ConZonotope.Real.ConZonotope
public import CORALean.ContSet.VPolytope.Real.VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.VPolytope_to_ConZonotope
public import CORALean.ContSet.Conversion.Real.Theorems.VPolytopeMemSimplexIff

@[expose] public section

/-!
# A hull as a constrained zonotope

Exact, and cheap: the vertices become the generators, the centre is the origin,
and the constraint polytope is the standard simplex — coefficients nonnegative
and summing to one.

The unit box a constrained zonotope also imposes costs nothing here. A
nonnegative coefficient in a family summing to one is already at most one, so
`|βⱼ| ≤ 1` is implied rather than imposed, and no vertex is lost.

This is the direction that makes a constrained zonotope the general representation: every bounded
polytope is one, with no enclosure anywhere.

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

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

-- the vertices become generators at a zero centre, so the two sets coincide
theorem VPolytope.conZonotope_exact (P : VPolytope α) :
    P.construct = P.conZonotope.construct := by -- --- PROOF ---
  ext x
  constructor
  · rintro ⟨β, hnn, hsum, rfl⟩
    refine ⟨β, fun j => ?_, VPolytope.mem_simplex_iff.mpr ⟨hnn, hsum⟩, ?_⟩
    · rw [abs_of_nonneg (hnn j)]
      exact hsum ▸ Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ j)
    · show ∑ j, β j • P.V j = 0 + ∑ j, β j • P.V j
      rw [zero_add]
  · rintro ⟨β, -, hβ, rfl⟩
    obtain ⟨hnn, hsum⟩ := VPolytope.mem_simplex_iff.mp hβ
    refine ⟨β, hnn, hsum, ?_⟩
    show (0 : α) + ∑ j, β j • P.V j = ∑ j, β j • P.V j
    rw [zero_add]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
