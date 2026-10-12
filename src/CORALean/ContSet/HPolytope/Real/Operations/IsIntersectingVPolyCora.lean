import CORALean.ContSet.HPolytope.Real.HPolytope
import CORALean.ContSet.VPolytope.Real.VPolytope
import Mathlib.Data.Fin.Tuple.Basic

/-!
# `HPolytope.isIntersectingVPolyCora`, CORA's H-polytope/V-polytope intersection test

CORA's `@polytope/isIntersecting_.m`, `aux_isIntersecting_Hpoly_Vpoly(P1,P2)` (l. 197-229),
reached from `aux_isIntersecting_poly_poly` (l. 173, and l. 177 with the arguments switched)
whenever one polytope is held in H-representation and the other in V-representation only. Its
comment states the program `A x ≤ b`, `Ae x = be`, `V β = x`, `∑ βⱼ = 1`, `β ≥ 0`, but the
coded `Aeq` is `[Ae 0; 0 1ᵀ]`: the coupling `V β = x` is missing. One `let` per line of the
source; the objective is `0`, so `CORAlinprog` (`linprog`, a caller's argument) answers on the
feasible set alone, and the verdict is `exitflag ≠ -2`.

## References

* [1] `contSet/@polytope/isIntersecting_.m`, CORA, ll. 161-183, 197-229.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1]'s `aux_isIntersecting_Hpoly_Vpoly` over the variable `(x, β)`, with `linprog` the
exit flag `CORAlinprog` returns on a feasible set. -/
def HPolytope.isIntersectingVPolyCora (P1 : HPolytope (Vec ℝ n)) (P2 : VPolytope (Vec ℝ n))
    (linprog : Set (Vec ℝ n × (Fin P2.k → ℝ)) → ℤ) : Bool :=
  -- l. 209-211: `nrIneq`, `nrEq`, `numVert`
  let nrIneq := P1.m
  let nrEq := P1.me
  let numVert := P2.k
  -- l. 214-215: `Aineq = [A, 0; 0, -eye(numVert)]`
  let Aineq : Fin (nrIneq + numVert) → Vec ℝ n × (Fin numVert → ℝ) → ℝ :=
    Fin.append (fun i z => P1.A i z.1) (fun j z => -z.2 j)
  -- l. 216: `bineq = [b; zeros(numVert,1)]`
  let bineq : Fin (nrIneq + numVert) → ℝ := Fin.append P1.b 0
  -- l. 217-218: `Aeq = [Ae, 0; 0, ones(1,numVert)]`, no `V β = x` row
  let Aeq : Fin (nrEq + 1) → Vec ℝ n × (Fin numVert → ℝ) → ℝ :=
    Fin.append (fun i z => P1.Ae i z.1) (fun _ z => ∑ j, z.2 j)
  -- l. 219: `beq = [be; 1]`
  let beq : Fin (nrEq + 1) → ℝ := Fin.append P1.be 1
  -- l. 224: `[~,val,exitflag] = CORAlinprog(problem)` (`f = 0`, no bounds)
  let exitflag := linprog {z | (∀ i, Aineq i z ≤ bineq i) ∧ ∀ i, Aeq i z = beq i}
  -- l. 227: `res = exitflag ~= -2`
  exitflag != -2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
