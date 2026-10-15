module

public import CORALean.ContSet.HPolytope.Real.HPolytope
public import CORALean.ContSet.StarSet.Real.StarSet
public import CORALean.Global.SupportFunction.SupportFunction

@[expose] public section

/-!
# A halfspace description as a star set

The identity map on the factors: the star set `{α | A α ≤ b, A_e α = b_e, l ≤ α ≤ u}` with the
rows of the polytope as its constraint rows, an equality as the two inequalities it stands for.
A star set is bounded, so the conversion takes the bounds the polytope's coordinates satisfy as
certificates, as `HPolytope.conZonotope` does, and they enter as `l` and `u`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The coefficients of a linear functional on `Vec ℝ n`: its value at each unit vector. -/
def HPolytope.coeffRow (f : Vec ℝ n →ₗ[ℝ] ℝ) : Fin n → ℝ :=
  fun k => f (fun j => if k = j then 1 else 0)

/-- The constraint rows of a halfspace description, `a · α ≤ b` read row by row. -/
def HPolytope.starRows (P : HPolytope (Vec ℝ n)) : List ((Fin n → ℝ) × ℝ) :=
  (List.finRange P.m).map (fun i => (HPolytope.coeffRow (P.A i), P.b i)) ++
    (List.finRange P.me).flatMap (fun i => [(HPolytope.coeffRow (P.Ae i), P.be i),
      (-HPolytope.coeffRow (P.Ae i), -P.be i)])

/-- The star set with the identity as its generators and the polytope's rows as its constraints,
the factors bounded by the certified bounds of the coordinates. -/
def HPolytope.starSet (P : HPolytope (Vec ℝ n))
    (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) : StarSet n where
  m := n
  c := 0
  G := fun i k => if i = k then 1 else 0
  cons := P.starRows
  l := fun j => -(lo j).val
  u := fun j => (up j).val

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
