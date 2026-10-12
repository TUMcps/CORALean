import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
import Mathlib.Data.Sign.Basic

/-!
# CORA's normal cone columns

`aux_normalCone` in `isPolytope` [1]: at a corner, the inward derivative per factor.
Zero columns, which CORA drops, add nothing to a cone and are kept.

## References

* [1] `contSet/@polyZonotope/isPolytope.m`, CORA (Sep. 2025), by N. Kochdumper (2019).
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Column `i` of `aux_normalCone` for the corner `I`: `Σ_{k : E(i,k) > 0} G(:,k) ∏ I^E(:,k) /
I(i)^E(i,k)`, then scaled by `-sign(I(i))`. -/
noncomputable def PolyZonotope.coraNormalCone (pZ : PolyZonotope α) (I : Fin pZ.p → ℝ)
    (i : Fin pZ.p) : α :=
  let column := ∑ k ∈ Finset.univ.filter (fun k => 0 < pZ.E i k),
    (PolyZonotope.monomial pZ.E I k / I i ^ pZ.E i k) • pZ.G k
  (-(SignType.sign (I i) : ℝ)) • column

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
