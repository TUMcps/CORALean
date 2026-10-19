module

public import CORALean.ContSet.HPolytope.Real.HPolytope
public import CORALean.ContSet.VPolytope.Real.VPolytope
public import Mathlib.Data.Fin.Tuple.Basic
public import CORALean.ContSet.HPolytope.Real.Operations.Ineqs
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `HPolytope.isIntersectingVPolyCora`, CORA's H-polytope/V-polytope intersection test

CORA's `@polytope/isIntersecting_.m`, `aux_isIntersecting_Hpoly_Vpoly(P1,P2)` (l. 197-229),
reached from `aux_isIntersecting_poly_poly` (l. 173, and l. 177 with the arguments switched)
whenever one polytope is held in H-representation and the other in V-representation only. Its
comment states the program `A x ≤ b`, `Ae x = be`, `V β = x`, `∑ βⱼ = 1`, `β ≥ 0`, but the
coded `Aeq` is `[Ae 0; 0 1ᵀ]`: the coupling `V β = x` is missing. One `let` per line of the
source; the objective is `0`, so `CORAlinprog` (`linprog`, a caller's argument) answers on the
feasible set alone, and the verdict is `exitflag ≠ -2`.

# CORA's H/V-polytope intersection test reports disjoint polytopes as intersecting

The unit box `[-1, 1]²` in H-representation and the triangle `conv{(5,5), (6,5), (5,6)}` in
V-representation are disjoint, yet the program of `HPolytope.isIntersectingVPolyCora` is
feasible (`x = 0`, `β = (1, 0, 0)`): without `V β = x` it only asks that the H-polytope be
nonempty. Every `CORAlinprog` that returns `-2` only on an infeasible program therefore makes
`isIntersecting(P1,P2)` (default `'exact'`) answer `true`; no earlier branch of
`isIntersecting_.m` intercepts (neither set is a fullspace or a halfspace, `n = 2`, no equality).

## References

* [1] `contSet/@polytope/isIntersecting_.m`, CORA, ll. 161-183, 197-229.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
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

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.isIntersectingVPolyCora_counterexample : -- --- CONCL ---
    let P1 : HPolytope (Vec ℝ 2) := HPolytope.ineqs !![1, 0; 0, 1; -1, 0; 0, -1] ![1, 1, 1, 1]
    let P2 : VPolytope (Vec ℝ 2) := ⟨3, ![![5, 5], ![6, 5], ![5, 6]]⟩
    Disjoint P1.construct P2.construct ∧
      ∀ linprog : Set (Vec ℝ 2 × (Fin P2.k → ℝ)) → ℤ, (∀ S, linprog S = -2 → S = ∅) →
        P1.isIntersectingVPolyCora P2 linprog = true := by -- --- PROOF ---
  intro P1 P2
  refine ⟨Set.disjoint_left.mpr fun x hx hx₂ => ?_, fun linprog hlp => ?_⟩
  -- `x₀ ≤ 1` in the box, `x₀ ≥ 5` in the triangle
  · have h0 := HPolytope.mem_ineqs_iff.mp hx 0
    obtain ⟨β, hβ, hs, rfl⟩ := hx₂
    simp [P2, mulVec, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three] at h0 hs
    linarith [hβ 0, hβ 1, hβ 2]
  -- the program is feasible at `x = 0`, `β = (1, 0, 0)`
  · simp only [HPolytope.isIntersectingVPolyCora, bne_iff_ne, ne_eq]
    intro h
    have hne := hlp _ h
    have hz : ((0 : Vec ℝ 2), (![1, 0, 0] : Fin P2.k → ℝ)) ∈
        (∅ : Set (Vec ℝ 2 × (Fin P2.k → ℝ))) := by
      rw [← hne]
      refine ⟨fun i => ?_, fun i => ?_⟩
      · refine Fin.addCases (fun i => ?_) (fun j => ?_) i
        · rw [Fin.append_left, Fin.append_left]
          change Fin 4 at i
          fin_cases i <;> simp [P1, HPolytope.ineqs]
        · rw [Fin.append_right, Fin.append_right]
          change Fin 3 at j
          fin_cases j <;> simp
      · refine Fin.addCases (fun i => i.elim0) (fun _ => ?_) i
        simp [P2, Fin.sum_univ_three]
    exact hz

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
