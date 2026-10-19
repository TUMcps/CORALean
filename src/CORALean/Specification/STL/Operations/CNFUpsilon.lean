module

public import CORALean.Specification.STL.Operations.RTLBigAnd
public import CORALean.Specification.STL.Operations.RTLBigOr
public import CORALean.Specification.STL.Definitions.SampledTime

@[expose] public section

/-!
# The transformation from sampled time STL to RTL

`Υ` of [1, Lemma 2], Eqs. (16) and (17), on a normal form: `⋁_k F(0,c)ϱ_k ∨ ⋁_l G(0,c)ϱ_l` becomes
`X_{c/2}(Aϱ' ∨ ⋁_l A(ϱ_l ∨ ϱ'))`, `ϱ' = ⋁_k ϱ_k`, and `ϱᵢⱼ` becomes `Aϱᵢⱼ` beside it.

Real-only, a specification: it rewrites or builds formulas, whose time bounds and constants are
part of the syntax and are copied or added exactly, never rounded.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Υ(⋀ᵢ ⋁ⱼ X_c^j (φᵢⱼ ∨ ϱᵢⱼ))`. -/
noncomputable def STL.CNF.upsilon (c : ℝ≥0) (cnf : STL.CNF X) : RTL.Formula X :=
  -- (17): `ϱ' := ⋁_k ϱ_k`
  let ϱ' := fun b : STL.Branch X => Pform.bigOr b.K
  -- (17): `Υ(φᵢⱼ) := X_{c/2}(Aϱ' ∨ ⋁_l A(ϱ_l ∨ ϱ'))`
  let Υφ := fun b : STL.Branch X =>
    RTL.Formula.next (c / 2) (.or (.A (ϱ' b))
      (RTL.Formula.bigOr (b.L.map fun ϱ => .A (.or ϱ (ϱ' b)))))
  -- (16): `Υ(X_c^j (φᵢⱼ ∨ ϱᵢⱼ)) := X_c^j (Υ(φᵢⱼ) ∨ Aϱᵢⱼ)`
  let branch := fun b : STL.Branch X => RTL.Formula.next (b.j * c) (.or (Υφ b) (.A b.ϱ))
  -- (16): `⋁ⱼ` inside a clause, `⋀ᵢ` across clauses
  RTL.Formula.bigAnd (cnf.map fun clause => RTL.Formula.bigOr (clause.map branch))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
