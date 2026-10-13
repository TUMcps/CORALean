module

public import CORALean.ContSet.Zonotope.Real.Operations.GenSelection

@[expose] public section

/-!
# `Alg. 1` lines 11-13: growing the selection until it covers

[1, Alg. 1] lines 11-13: one more generator while the selection, read at the
subtrahend's centre, still does not enclose it — the test through the
caller's own `encloses`, zonotope-in-zonotope containment having no decision
procedure here.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 11-13: one more generator while the selection, read at the
subtrahend's centre, still does not enclose it. -/
def Zonotope.enclCoverLoop (encloses : Zonotope (Vec ℝ n) → Bool) (Z : Zonotope (Vec ℝ n))
    (σ : Equiv.Perm (Fin Z.h)) (cs : Vec ℝ n) : ℕ → ℕ → ℕ
  | 0, ξ => ξ
  | k + 1, ξ =>
    if ξ < Z.h ∧ encloses (Z.genSelection σ cs ξ) = false then
      Z.enclCoverLoop encloses σ cs k (ξ + 1)
    else ξ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
