import CORALean.HybridDynamics.Operations.IdentGuard
import Mathlib.Tactic.Linarith

/-!
# The guard of Prop. 1 is exactly the states the reset maps into the target invariant

[1, Prop. 1]: on the surface `H = ⟨a, b, [], []⟩_H` with reset `r(x) = H x + k` and target
invariant `Y = ⟨C, d⟩_P`, `G = ⟨a, b, C H, d - C k⟩_H` is `{x ∈ H | r(x) ∈ Y}`, the paper's
chain of equalities: every state entering `G` is mapped into `Y`, and no state of `H` that would
be is left out.

## References

* [1] N. Kochdumper, M. A. Foughali, P. Habermehl and E. Asarin. "Robust Identification of
      Hybrid Automata from Noisy Data". In Proc. of the 28th ACM International Conference on
      Hybrid Systems: Computation and Control (HSCC), pp. 1-11, 2025.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 1]: `⟨a, b, C H, d - C k⟩_H = {x | aᵀx = b ∧ H x + k ∈ ⟨C, d⟩_P}`. -/
theorem IdentHA.conHyperplane_identGuard (a : Vec ℝ n) (b : ℝ) (H : Mat ℝ n n) (k : Vec ℝ n)
    (cs : List (Vec ℝ n × ℝ)) :
    IdentHA.conHyperplane a b (IdentHA.identGuard H k cs)
      = {x | a ⬝ᵥ x = b ∧ H *ᵥ x + k ∈ IdentHA.polySet cs} := by -- --- PROOF ---
  ext x
  -- `cᵀ(H x + k) = (Hᵀc)ᵀx + cᵀk`
  have hid : ∀ c : Vec ℝ n, c ⬝ᵥ (H *ᵥ x + k) = (Hᵀ *ᵥ c) ⬝ᵥ x + c ⬝ᵥ k := fun c => by
    rw [dotProduct_add, dotProduct_mulVec, mulVec_transpose]
  simp only [IdentHA.conHyperplane, IdentHA.polySet, IdentHA.identGuard, Set.mem_setOf_eq,
    List.mem_map, forall_exists_index, and_imp]
  refine and_congr_right fun _ => ⟨fun h q hq => ?_, fun h p q hq hp => ?_⟩
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
