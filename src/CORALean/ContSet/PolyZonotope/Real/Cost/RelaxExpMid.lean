import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpMid
import CORALean.ContSet.PolyZonotope.Real.Cost.RelaxDrift

/-!
# `PolyZonotope.relaxExpMidCost`

Asserted, not proved, at `Vec ℝ n`: `Operations/RelaxExpMid.lean` evaluates
`relaxDrift` twice, once for the centre's shift (`n` products, `n` additions)
and once for the new generator's radius (`n` products), and adds the two named
generators (`n`).
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.relaxExpMid` costs at `Vec ℝ n` and `p` factors. -/
def PolyZonotope.relaxExpMidCost (n p : ℕ) : Cost :=
  ⟨4 * n⟩ + (2 : ℕ) • PolyZonotope.relaxDriftCost p

/-- Monotone in the factor count. -/
theorem PolyZonotope.relaxExpMidCost_mono {p p' : ℕ} (n : ℕ) (h : p ≤ p') :
    PolyZonotope.relaxExpMidCost n p ≤ PolyZonotope.relaxExpMidCost n p' := by
  have := PolyZonotope.relaxDriftCost_mono h
  simp only [PolyZonotope.relaxExpMidCost, Cost.le_iff, Cost.ops_add, Cost.ops_smul] at this ⊢
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
