import CORALean.ContSet.PolyZonotope.Real.Operations.CoraVertex
import CORALean.ContSet.PolyZonotope.Real.Operations.CoraNormalCone
import CORALean.ContSet.PolyZonotope.Real.Operations.InCone

/-!
# The `true` path of CORA's `isPolytope`

The `true` path of `isPolytope` [1], with the linear program replaced by cone membership and
the hull vertices given as corner assignments (`convhulln` is not modelled).

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

/-- The `true` path of `isPolytope`, given the corners `I` of the hull vertices: no exponent `≥ 2`,
and from every hull vertex `v` the difference to every other one lies in the cone of its inward
derivatives. -/
def PolyZonotope.coraAccepts {m : ℕ} (pZ : PolyZonotope α) (corners : Fin m → Fin pZ.p → ℝ) :
    Prop :=
  (∀ i k, pZ.E i k < 2) ∧
    ∀ s t, pZ.coraVertex (corners s) ≠ pZ.coraVertex (corners t) →
      inCone (pZ.coraNormalCone (corners s))
        (pZ.coraVertex (corners t) - pZ.coraVertex (corners s))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
