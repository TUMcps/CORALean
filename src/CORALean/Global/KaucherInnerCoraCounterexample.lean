module

public import CORALean.Global.KaucherInner
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# CORA reports `(-∞, ∞)` where (18) gives no inner approximation

When a component of [1, Eq. 18] comes out proper, [1, Alg. 1, Step 3] says the inner
approximation is empty. CORA's `priv_reachInnerProjection` stores `interval(-inf, inf)` for
such a component instead (its `isProp` returns `inf >= sup`, i.e. improper, and the branch
for `~isProp` writes the whole line), which no bounded reachable set contains. For
`ż = 0` on `[0, 1]` with `z̃₀ = ½`, the sound but loose `[z̃] = [-1, 2]` and `[J] = [1, 1]`,
(18) is `[-½, 3/2]`, proper, and CORA's component is `ℝ` against the range `[0, 1]`
(read from the source, not run).

## References

* [1] E. Goubault and S. Putot. "Forward Inner-Approximated Reachability of Non-Linear
      Continuous Systems". In Proc. of the 20th International Conference on Hybrid Systems:
      Computation and Control (HSCC), pp. 1-10, 2017.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set


-- =======================================  MAIN THEOREM  ======================================= --

/-- A proper result of (18) at valid enclosures, where the whole line CORA reports is not in
the range. -/
theorem kaucherInnerStep_cora_counterexample :
    let s := kaucherInnerStep (n := 1) (fun _ => -1) (fun _ => 2) (fun _ _ => 1) (fun _ _ => 1)
      (fun _ => 0) (fun _ => 1) (fun _ => 1 / 2) 0
    s.1 < s.2 ∧ (fun _ => (1 / 2 : ℝ)) 0 ∈ Icc (-1 : ℝ) 2 ∧
      ¬ (univ : Set ℝ)
        ⊆ (fun z : Fin 1 → ℝ => z 0) '' Icc (fun _ => 0) (fun _ => 1) := by -- --- PROOF ---
  refine ⟨by norm_num [kaucherInnerStep, kaucherMulDualZ], by norm_num, fun h => ?_⟩
  obtain ⟨z, hz, h2⟩ := h (mem_univ (2 : ℝ))
  have := hz.2 0
  simp only at h2 this
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
