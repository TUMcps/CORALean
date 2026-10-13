import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# `evaluatePredicateUnionCora`, the union-of-unsafe-sets branch of CORA's `aux_evaluatePredicate`

The `else` branch (`% union of unsafe sets`) of `aux_evaluatePredicate` in CORA's
`@linearSys/private/priv_verifySTL_kochdumper.m` (l. 886-957), the program of [1]: the status of a
reachable zonotope `R = (c, G)` against unsafe halfspaces `{x | cᵀx ≤ d}` (`set{i}.c'`,
`set{i}.d`), as printed, one `let` per MATLAB step: `c = c'·R.c`, `G = c'·R.G`, `G = abs(G)`,
`rad = sum(G,2)`, the quick checks (`1` disjoint, `0` contained, returning at once, `3` meeting on
the initial and input factors, else `2`, where a polytope would call `isIntersecting`, which a
halfspace skips), `list(i) = res`. The branch ends `res = max(list(i))`, the last set's entry and
not `max(list)`: unless an earlier set returned `0`, the answer is the code of the last set alone.
`index` is `ind.int{i}` or `ind.point{i}`, the columns of `R.G` for the initial and input factors.

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

/-- CORA's union branch of `aux_evaluatePredicate` for `R = Rc + Rg·[-1,1]^m` and the unsafe
halfspaces `(cᵢ, dᵢ)`: `0` when some set contains `R` (checked in order), else the code of the
last set. -/
noncomputable def STL.evaluatePredicateUnionCora {n m : ℕ} (Rc : Fin n → ℝ)
    (Rg : Fin n → Fin m → ℝ) (index : Finset (Fin m)) :
    List ((Fin n → ℝ) × ℝ) → ℕ
  | [] => 0
  | (cs, d) :: rest =>
    let c := ∑ j, cs j * Rc j                                  -- c = set{i}.c' * R.c
    let G := fun k => ∑ j, cs j * Rg j k                       -- G = set{i}.c' * R.G
    let G := fun k => |G k|                                    -- G = abs(G)
    let rad := ∑ k, G k                                        -- rad = sum(G,2)
    let res : ℕ :=
      if c - rad > d then 1                                    -- any(c - rad > d): res = 1
      else if c + rad ≤ d then 0                               -- all(c + rad <= d): res = 0
      else if c + ∑ k ∈ index, G k ≤ d then 3                  -- all(c + sum(G(:,index),2) <= d)
      else 2                                                   -- res = 2 (a halfspace: no more)
    if res = 0 then 0                                          -- res = 0; return
    else if rest = [] then res                                 -- res = max(list(i)), i = last
    else STL.evaluatePredicateUnionCora Rc Rg index rest

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
