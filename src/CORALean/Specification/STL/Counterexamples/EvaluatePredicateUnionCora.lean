module

public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# `evaluatePredicateUnionCora`, the union-of-unsafe-sets branch of CORA's `aux_evaluatePredicate`

The `else` branch (`% union of unsafe sets`) of `aux_evaluatePredicate` in CORA's
`@linearSys/private/priv_verifySTL_kochdumper.m` (l. 886-957), the program of [1]: the status of a
reachable zonotope `R = (c, G)` against unsafe halfspaces `{x | cᵀx ≤ d}`, one `let` per MATLAB
step: `c = c'·R.c`, `G = abs(c'·R.G)`, `rad = sum(G,2)`, the quick checks (`1` disjoint, `0`
contained, `3` meeting on the initial and input factors, else `2`), `list(i) = res`. It ends
`res = max(list(i))`, the last set's entry and not `max(list)`.

# CORA's `aux_evaluatePredicate` reports a set meeting an earlier unsafe set as disjoint

Only the last unsafe set's code is returned (l. 955). In `ℝ¹` take `R = 0 + 1·[-1,1]` and the
halfspaces `x ≤ 0` and `x ≤ -5`: `R` meets the first (code `2`), the second is disjoint, and CORA
returns `1`. Downstream (read, not run), `aux_modelCheckReachSet` (l. 198-208) and `sampledTime`
then replace the predicate by `true`, so the verifier can answer `verified` for a reachable set
that meets an unsafe set. Only the helper is formalized here.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA reports a set meeting an earlier unsafe set as disjoint

## References

* [1] [N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, 2024.](../../../../../references/2024/kochdumper-nahs-stl-lti-verification.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- The model: CORA's code as printed, kept only to be refuted.
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


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.evaluatePredicateUnionCora_lastOnly_counterexample : -- --- CONCL ---
    let Rc : Fin 1 → ℝ := fun _ => 0
    let Rg : Fin 1 → Fin 1 → ℝ := fun _ _ => 1
    let S₁ : (Fin 1 → ℝ) × ℝ := (fun _ => 1, 0)      -- x ≤ 0
    let S₂ : (Fin 1 → ℝ) × ℝ := (fun _ => 1, -5)     -- x ≤ -5
    -- `R` meets the first unsafe set
    (∃ a : Fin 1 → ℝ, (∀ k, a k ∈ Set.Icc (-1 : ℝ) 1) ∧
      ∑ j, S₁.1 j * (Rc j + ∑ k, Rg j k * a k) ≤ S₁.2) ∧
    -- its code alone is `2`: partially intersecting
    STL.evaluatePredicateUnionCora Rc Rg {0} [S₁] = 2 ∧
    -- CORA's code for the union is `1`: disjoint
    STL.evaluatePredicateUnionCora Rc Rg {0} [S₁, S₂] = 1 := by -- --- PROOF ---
  intro Rc Rg S₁ S₂
  have h0 : (0 : ℝ) < 1 := one_pos
  refine ⟨⟨fun _ => 0, fun k => by simp, by simp [Rc, S₁]⟩, ?_, ?_⟩
  · simp [STL.evaluatePredicateUnionCora, Rc, Rg, S₁]
    simp only [not_lt.mpr h0.le, not_le.mpr h0, if_false]
    norm_num
  · simp [STL.evaluatePredicateUnionCora, Rc, Rg, S₁, S₂]
    simp only [not_lt.mpr h0.le, not_le.mpr h0, if_false]
    norm_num

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
