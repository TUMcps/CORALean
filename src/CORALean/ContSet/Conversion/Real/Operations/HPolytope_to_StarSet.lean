module

public import CORALean.ContSet.HPolytope.Real.Instances
public import CORALean.ContSet.StarSet.Real.StarSet
public import CORALean.Global.SupportFunction.SupportFunction

@[expose] public section

/-!
# A halfspace description as a star set

The identity map on the factors: the star set `{α | A α ≤ b, A_e α = b_e, l ≤ α ≤ u}` with the
polytope itself as its predicate. A star set is bounded, so the conversion takes the bounds the
polytope's coordinates satisfy as certificates, as `HPolytope.conZonotope` does, and they enter as
the coefficient box `[l, u]`.

## Inputs
* `P` – halfspace polytope

## Hypotheses
* `up` – certified upper bound per coordinate
* `lo` – certified lower bound per coordinate

## Output
* star set with identity generators and the polytope as predicate
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The star set with the identity as its generators and the polytope as its predicate, the
coefficient box the certified bounds of the coordinates. -/
def HPolytope.starSet (P : HPolytope (Vec ℝ n))
    (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) : StarSet ℋ𝒫 n where
  m := n
  c := 0
  G := fun i k => if i = k then 1 else 0
  dom := ⟨fun j => -(lo j).val, fun j => (up j).val⟩
  pred := P

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
