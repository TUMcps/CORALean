module

public import CORALean.ContSet.Zonotope.Real.Operations.Inclusion
public import CORALean.ContSet.Zonotope.Real.Operations.Plus
public import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope

@[expose] public section

/-!
# The mean-value inclusion function into a zonotope

[1, Thm. 5]: `Ψ(X, W) = q ⊕ S Bⁿ ⊕ ⋄M Bᵐ`, the zonotope `q ⊕ S Bⁿ = □f(p, W)` of the natural
interval extension of `f` at the centre, plus the zonotope inclusion `⋄M Bᵐ` of the interval matrix
`M = □∇ₓf(X, W) H` ([1, Thm. 4]). Both are arguments: `I` is the box `□f(p, W)` and `IM` the
interval matrix, and the enclosure `f(X, W) ⊆ Ψ(X, W)` holds for any that satisfy the hypotheses of
`image_subset_meanValueInclusion`. `2n + m` generators, as the paper states.

## References

* [1] T. Alamo, J. M. Bravo and E. F. Camacho. "Guaranteed state estimation by zonotopes".
      Automatica, 41(6):1035-1043, 2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `⋄M Bᵐ ⊕ (q ⊕ S Bⁿ)`: the inclusion of `IM` at centre `0`, plus the box `I` as a zonotope. -/
noncomputable def Zonotope.meanValueInclusion {n m : ℕ} (I : Interval (Vec ℝ n))
    (IM : Interval (Mat ℝ n m)) : Zonotope (Vec ℝ n) :=
  (Zonotope.inclusion 0 IM).plus I.zonotope

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
