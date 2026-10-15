module

public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Ellipsoid.Real.Theorems.Convex
public import CORALean.ContSet.Ellipsoid.Real.Theorems.IsCompact
public import CORALean.ContSet.Ellipsoid.Real.Theorems.SupportBoundAttained
public import CORALean.ContSet.SupportFunction.Real.Theorems.OfSetExact

@[expose] public section

/-!
# An ellipsoid as a support function

Exact. The closed form `ℓ c + ‖Gᵀ ℓ‖₂` bounds the ellipsoid and is attained
(`Ellipsoid.supportBound_attained`), so it is the support function of the set, which is closed and
convex and so denoted by it.

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

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.supportFunction_exact (E : Ellipsoid n) :
    E.supportFunction.construct = E.construct := by -- --- PROOF ---
  -- the closed form is the support function of the set: it bounds it, and is attained
  have h : E.supportFunction = SupportFunction.ofSet E.construct := by
    refine congrArg SupportFunction.mk (funext fun ℓ => le_antisymm ?_ ?_)
    · obtain ⟨x, hx, hxv⟩ := E.supportBound_attained ℓ
      exact hxv ▸ le_iSup₂ (f := fun y _ => (ℓ y : EReal)) x hx
    · exact iSup₂_le fun y hy => EReal.coe_le_coe_iff.mpr ((E.supportBound ℓ).le y hy)
  rw [h]
  exact SupportFunction.ofSet_exact E.convex_construct E.isCompact_construct.isClosed

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
