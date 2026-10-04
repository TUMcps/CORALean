import CORALean.ContSet.HPolytope.Real.Operations.RowNorm

/-!
# `HPolytope.IsLPCentre`

The centre of CORA's `@polytope/center` with the default method `'chebyshev'`, `aux_center_LP`: the
linear program `max r  s.t.  A x + ‖aᵢ‖₂ r ≤ b,  Aₑ x = bₑ,  r ≥ 0`, whose optimal `x` is returned.
An optimum cannot be computed here, so the centre is the specification: `x` is a centre when some
radius `r` is feasible with it and no feasible pair has a larger one. Every optimal `x` is a
centre, and nothing says one exists: an unbounded program (no row bounds `r`) has none.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `x` is an optimal solution of `aux_center_LP`. -/
def HPolytope.IsLPCentre (P : HPolytope (Vec ℝ n)) (x : Vec ℝ n) : Prop :=
  ∃ r : ℝ, 0 ≤ r ∧ (∀ i, P.A i x + HPolytope.rowNorm (P.A i) * r ≤ P.b i)
    ∧ (∀ i, P.Ae i x = P.be i)
    ∧ ∀ (x' : Vec ℝ n) (r' : ℝ), 0 ≤ r' → (∀ i, P.A i x' + HPolytope.rowNorm (P.A i) * r' ≤ P.b i)
        → (∀ i, P.Ae i x' = P.be i) → r' ≤ r


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
