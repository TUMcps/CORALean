module

public import CORALean.HybridDynamics.Operations.IdentGuard
public import CORALean.HybridDynamics.Theorems.IdentPolytopeMem
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The guard of Prop. 1 is exactly the states the reset maps into the target invariant

[1, Prop. 1]: on the surface `H = ⟨a, b, [], []⟩_H` with reset `r(x) = H x + k` and target
invariant `Y = ⟨C, d⟩_P`, `G = ⟨a, b, C H, d - C k⟩_H` is `{x ∈ H | r(x) ∈ Y}`, the paper's
chain of equalities: no state of `H` that `r` maps into `Y` is left out of `G`. That every state
of `G` is mapped into `Y` is `identGuard_maps_into`, the statement of the proposition.

## Inputs
* `a` – hyperplane normal
* `b` – hyperplane offset
* `H` – reset matrix
* `k` – reset offset
* `cs` – invariant rows

## Hypotheses
* none

## Conclusion
* the guard is the states the reset maps into the invariant

## References

* [1] [N. Kochdumper, M. A. Foughali, P. Habermehl and E. Asarin. "Robust Identification of Hybrid
      Automata from Noisy Data". Proceedings of the 28th ACM International Conference on Hybrid
      Systems: Computation and Control,
      2025.](../../../../references/2025/kochdumper-hscc-hybrid-automata-identification.md)
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       04-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 1], as an equality: the guard `⟨a, b, C H, d - C k⟩_H` is exactly the states of the
surface `aᵀx = b` that the reset `H x + k` maps into `Y = ⟨C, d⟩_P`. -/
theorem IdentHA.conHyperplane_identGuard (a : Vec ℝ n) (b : ℝ) (H : Mat ℝ n n) (k : Vec ℝ n)
    (cs : List (Vec ℝ n × ℝ)) : -- --- CONCL ---
    IdentHA.conHyperplane a b (IdentHA.identGuard H k cs)
      = {x | a ⬝ᵥ x = b ∧ H *ᵥ x + k ∈ (IdentHA.polytope cs).construct} := by -- --- PROOF ---
  ext x
  -- `cᵀ(H x + k) = (Hᵀc)ᵀx + cᵀk`
  have hid : ∀ c : Vec ℝ n, c ⬝ᵥ (H *ᵥ x + k) = (Hᵀ *ᵥ c) ⬝ᵥ x + c ⬝ᵥ k := fun c => by
    rw [dotProduct_add, dotProduct_mulVec, mulVec_transpose]
  simp only [IdentHA.conHyperplane, IdentHA.identGuard, Set.mem_setOf_eq]
  refine and_congr_right fun _ => ?_
  rw [IdentHA.mem_polytope_construct_iff, IdentHA.mem_polytope_construct_iff]
  simp only [List.mem_map, forall_exists_index, and_imp]
  refine ⟨fun h q hq => ?_, fun h p q hq hp => ?_⟩
  · have := h _ q hq rfl
    rw [hid]
    linarith
  · subst hp
    have := h q hq
    rw [hid] at this
    show (Hᵀ *ᵥ q.1) ⬝ᵥ x ≤ q.2 - q.1 ⬝ᵥ k
    linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
