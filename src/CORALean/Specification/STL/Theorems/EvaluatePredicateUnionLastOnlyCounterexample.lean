module

public import CORALean.Specification.STL.Operations.EvaluatePredicateUnionCora

@[expose] public section

/-!
# CORA's `aux_evaluatePredicate` reports a set meeting an earlier unsafe set as disjoint

`res = max(list(i))` ends the union branch of `aux_evaluatePredicate`
(`@linearSys/private/priv_verifySTL_kochdumper.m`, l. 955) with `i` the last loop index, so only
the last unsafe set's code is returned. In `ℝ¹` take `R = 0 + 1·[-1,1]` and the unsafe
halfspaces `x ≤ 0` and `x ≤ -5`: `R` meets the first (at `x = 0`), whose code alone is `2`,
but the second is disjoint from `R` (`c - rad = -1 > -5`), and CORA returns `1`, `disjoint`.

Downstream (read, not run): `aux_modelCheckReachSet` (l. 198-208) copies every entry `< 2`
of `pred` into the time point entries, and `sampledTime` (via `evalPredicates`, l. 68-69: `1` is
`satisfied`) then replaces the predicate by `true`, so no constraint on the factors from the missed
unsafe set is ever formed (`aux_getConstraints` is only reached for what is left of the formula):
the verifier can answer `verified` for a reachable set that meets an unsafe set. Only the helper
is formalized here, for the verifier of [1].

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


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.evaluatePredicateUnionCora_lastOnly_counterexample :
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
