import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# `safeToUnsafeCora`, CORA's complement of a union of safe polytopes

`aux_safe2unsafe` with `aux_reverseHalfspaceConstraints` in CORA's
`@linearSys/private/priv_verifySTL_kochdumper.m` (l. 827-870, the program of [1]), the union of
unsafe sets that `aux_preprocessTemporalLogic` (l. 959-991) makes of a predicate whose disjunctive
normal form has two or more clauses, one `let` per MATLAB step. A polytope is the list of its rows
`(Aⱼ, bⱼ)`, `{x | Aⱼx ≤ bⱼ}`. Each row is reversed by `polytope/not` to the one-row polytope `(-Aⱼ,
-bⱼ - eps)`; the list starts with the reversed rows of the first clause, and each further clause
replaces it by `list{k} & reversed{j}` (rows of `list{k}`, then the reversed row) for every reversed
row `j` (outer loop) and every `k` (inner loop) with `isIntersecting(list{k}, reversed{j})`.
`isIntersecting` is a parameter on the two polytopes as sets; `eps` is MATLAB's.

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, vol. 53, 2024, 101491.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `aux_safe2unsafe` on the safe polytopes `clauses`: the unsafe polytopes whose union is
the complement of their union (up to `eps`), in CORA's order. -/
noncomputable def STL.safeToUnsafeCora {n : ℕ}
    (isIntersecting : Set (Fin n → ℝ) → Set (Fin n → ℝ) → Bool) (eps : ℝ) :
    List (List ((Fin n → ℝ) × ℝ)) → List (List ((Fin n → ℝ) × ℝ))
  | [] => []
  | S₁ :: rest =>
    let poly := fun P : List ((Fin n → ℝ) × ℝ) =>
      {x : Fin n → ℝ | ∀ r ∈ P, ∑ j, r.1 j * x j ≤ r.2}             -- polytope(P)
    let reverse := fun P : List ((Fin n → ℝ) × ℝ) =>
      P.map fun r => [(-r.1, -r.2 - eps)]                           -- ~polytope(P.A(i,:),P.b(i))
    let list := reverse S₁                                          -- list = aux_reverse...
    rest.foldl (fun list Sᵢ =>                                      -- for i = 2:length(sets)
      let reversed := reverse Sᵢ                                    -- reversedHalfspaces
      reversed.flatMap fun h =>                                     -- for j
        list.filterMap fun L =>                                     -- for k
          if isIntersecting (poly L) (poly h) then some (L ++ h)    -- list_{end+1} = ... & ...
          else none) list                                           -- list = list_

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
