import CORALean.ContSet.LevelSet.Real.Operations.IntersectLevelSetBox

/-!
# [1, Thm. 1]'s exactness fails when `p_k` depends on `x(k)`

In `ℝ¹` with `I = [0, 1]` and `p(x) = x/2`, condition (4) holds — `p(I) = [0, ½] ⊆ [0, 1]` —
and `LS = {x | x = x/2} = {0}`, so `I ∩ LS = {0}`; the model is `{x/2 | x ∈ I} = [0, ½]`,
which contains `½`. Printed with `LS = {x | x(k) = p_k(x)}` and no condition on `p_k`'s
variables, the theorem claims these equal; `IntersectLevelSetBoxExact` adds the missing one.

## References

* [1] N. Kochdumper and M. Althoff. "Reachability Analysis for Hybrid Systems with Nonlinear
      Guard Sets". In Proc. of the 23rd ACM International Conference on Hybrid Systems:
      Computation and Control (HSCC), 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem intersectLevelSetBox_exact_counterexample :
    let I : Interval (Vec ℝ 1) := ⟨fun _ => 0, fun _ => 1⟩
    let p : Vec ℝ 1 → ℝ := fun x => x 0 / 2
    (∀ x ∈ I.construct, I.inf 0 ≤ p x ∧ p x ≤ I.sup 0) ∧
      I.construct ∩ {x | x 0 = p x} ≠ (intersectLevelSetBox I 0 p).construct := by -- --- PROOF ---
  intro I p
  refine ⟨fun x hx => ?_, fun heq => ?_⟩
  · have h : 0 ≤ x 0 ∧ x 0 ≤ 1 := hx 0
    simp only [I, p]
    constructor <;> linarith [h.1, h.2]
  · -- `½` is the image of `1`, but not a fixed point of `p`
    have hmem : (fun _ => (1 / 2 : ℝ)) ∈ (intersectLevelSetBox I 0 p).construct := by
      refine ⟨fun _ => 1, fun _ => ?_, 0, fun _ => ⟨le_rfl, le_rfl⟩, ?_⟩
      · show (0 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 1
        norm_num
      · funext i
        rw [Fin.fin_one_eq_zero i]
        simp [intersectLevelSetBox, p]
    rw [← heq] at hmem
    have h := hmem.2
    simp only [Set.mem_setOf_eq, p] at h
    norm_num at h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
