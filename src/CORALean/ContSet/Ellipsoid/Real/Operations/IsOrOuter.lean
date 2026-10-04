import CORALean.ContSet.Ellipsoid.Real.Operations.Mtimes

/-!
# `Ellipsoid.IsOrOuter`

What CORA's `or(E₁, E₂, 'outer')` (`priv_orEllipsoidOA`) owes: its ellipsoid contains both operands.
CORA returns a minimum-volume such ellipsoid from an SDP solver (MOSEK, SDPT3 or YALMIP), after
bloating degenerate operands; only the enclosure is formalized, not the minimum volume.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `E` contains both `E₁` and `E₂`. -/
def Ellipsoid.IsOrOuter (E₁ E₂ E : Ellipsoid n) : Prop :=
  E₁.construct ∪ E₂.construct ⊆ E.construct


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
