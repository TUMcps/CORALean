module

public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# `evaluatePredicateUnionPolytopeCora`, the union branch of `aux_evaluatePredicate` on polytopes

The `else` branch (`% union of unsafe sets`) of `aux_evaluatePredicate` in CORA's
`@linearSys/private/priv_verifySTL_kochdumper.m` (l. 916-956, the program of [1]) for unsafe sets
that are polytopes `{x | Aᵢx ≤ bᵢ}`, the only kind `aux_safe2unsafe` builds (`polytope(list{k}) &
polytope(...)`, l. 849), one `let` per MATLAB step: `c = set{i}.A·R.c`, `G = set{i}.A·R.G`, `G =
abs(G)`, `rad = sum(G,2)`, the quick checks (`any(c - rad > d)`: `1`; `all(c + rad <= d)`: `0`,
returning at once; `all(c + sum(G(:,index),2) <= d)`: `3`), else `2`, lowered to `1` when
`~isIntersecting(R,set{i})`, then `list(i) = res`; the branch ends `res = max(list(i))`, the last
set's code. A polytope is the list of its rows `(Aⱼ, bⱼ)`; `isIntersecting` is a parameter, on the
zonotope `R = Rc + Rg·[-1,1]^m` and the polytope as sets. The halfspace arm, which skips
`isIntersecting`, is `STL.evaluatePredicateUnionCora`.

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, vol. 53, 2024, 101491.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's union branch of `aux_evaluatePredicate` for `R = Rc + Rg·[-1,1]^m` and unsafe
polytopes given by their rows: `0` when some set contains `R` (checked in order), else the code of
the last set. -/
noncomputable def STL.evaluatePredicateUnionPolytopeCora {n m : ℕ}
    (isIntersecting : Set (Fin n → ℝ) → Set (Fin n → ℝ) → Bool) (Rc : Fin n → ℝ)
    (Rg : Fin n → Fin m → ℝ) (index : Finset (Fin m)) :
    List (List ((Fin n → ℝ) × ℝ)) → ℕ
  | [] => 0
  | P :: rest =>
    let c := fun r : (Fin n → ℝ) × ℝ => ∑ j, r.1 j * Rc j          -- c = set{i}.A * R.c
    let G := fun (r : (Fin n → ℝ) × ℝ) k => ∑ j, r.1 j * Rg j k     -- G = set{i}.A * R.G
    let G := fun r k => |G r k|                                     -- G = abs(G)
    let rad := fun r => ∑ k, G r k                                  -- rad = sum(G,2)
    let R : Set (Fin n → ℝ) := {x | ∃ a : Fin m → ℝ, (∀ k, a k ∈ Set.Icc (-1 : ℝ) 1) ∧
      x = fun j => Rc j + ∑ k, Rg j k * a k}                         -- R
    let S : Set (Fin n → ℝ) := {x | ∀ r ∈ P, ∑ j, r.1 j * x j ≤ r.2}  -- set{i}
    let res : ℕ :=
      if ∃ r ∈ P, c r - rad r > r.2 then 1                          -- any(c - rad > d): res = 1
      else if ∀ r ∈ P, c r + rad r ≤ r.2 then 0                     -- all(c + rad <= d): res = 0
      else if ∀ r ∈ P, c r + ∑ k ∈ index, G r k ≤ r.2 then 3       -- all(c + sum(G(:,index),2)...)
      else if isIntersecting R S = false then 1                     -- ~isIntersecting(R,set{i})
      else 2                                                        -- res = 2
    if res = 0 then 0                                               -- res = 0; return
    else if rest = [] then res                                      -- res = max(list(i)), i = last
    else STL.evaluatePredicateUnionPolytopeCora isIntersecting Rc Rg index rest

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
