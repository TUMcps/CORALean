module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.IsCompact
public import CORALean.ContSet.SupportFunction.Real.SupportFunction

@[expose] public section

/-!
# A support function that is no ellipsoid

An ellipsoid is a support function (`Ellipsoid.supportFunction_exact`), and the inclusion is strict:
a support function may be `+∞` and denote the whole space, which no ellipsoid does, being compact.

This is the arrow from ellipsoids to support functions of
[1, Fig. 1 (Ellipsoids → Support Functions)].

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

theorem SupportFunction.exists_not_ellipsoid :
    ∃ S : SupportFunction (Vec ℝ 1),
      ¬ ∃ E : Ellipsoid 1, E.construct = S.construct := by -- --- PROOF ---
  refine ⟨⟨fun _ => ⊤⟩, ?_⟩
  rintro ⟨E, hE⟩
  -- the support function with value `+∞` everywhere denotes the whole space
  have huniv : (SupportFunction.construct ⟨fun _ => ⊤⟩ : Set (Vec ℝ 1)) = Set.univ :=
    Set.eq_univ_of_forall fun x ℓ => le_top
  rw [huniv] at hE
  -- which is not compact
  have hc : IsCompact (Set.univ : Set (Vec ℝ 1)) := hE ▸ E.isCompact_construct
  exact NoncompactSpace.noncompact_univ hc

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
