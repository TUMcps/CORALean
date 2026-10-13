import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.HPolytope.Real.Operations.MinkDiff1DCora
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# CORA's 1-D polytope `minkDiff` with a one-sided subtrahend is not inner

The minuend `P = [-1, 1]` compacts to the rows `x ≤ 1`, `-x ≤ 1`; the subtrahend `S = {x ≤ 0}`
compacts to its single row `x ≤ 0` (`priv_compact_1D`, l. 77-89: `b = [0; min([])] = 0`, one
inequality, `A = 1`). `HPolytope.minkDiff1DCora` subtracts the offset `0` from both rows of the
minuend and returns `[-1, 1]` again, while `P ⊖ S` is empty: `S` is unbounded below and `P` is
not. So `0` is in CORA's result although `0 + (-2) ∉ P`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.minkDiff1DCora_counterexample :
    let P_ : HPolytope (Vec ℝ 1) :=
      ⟨2, ![LinearMap.proj 0, -LinearMap.proj 0], ![1, 1], 0, Fin.elim0, Fin.elim0⟩
    let S_ : HPolytope (Vec ℝ 1) := ⟨1, ![LinearMap.proj 0], ![0], 0, Fin.elim0, Fin.elim0⟩
    ∃ Q, P_.minkDiff1DCora S_ = some Q ∧ (0 : Vec ℝ 1) ∈ Q.construct ∧
      minkowskiDiff P_.construct S_.construct = ∅ := by -- --- PROOF ---
  intro P_ S_
  -- `2 ∉ P_`, `0 ∈ S_`: no early return
  have hP : P_.construct ≠ Set.univ := fun h => by
    have h2 : (fun _ => 2 : Vec ℝ 1) ∈ P_.construct := h ▸ Set.mem_univ _
    have := h2.1 (show Fin 2 from 0)
    simp [P_] at this
  have hS : S_.construct ≠ ∅ := fun h => by
    have h0 : (0 : Vec ℝ 1) ∈ S_.construct :=
      ⟨fun i => by fin_cases i; simp [S_], fun i => i.elim0⟩
    rw [h] at h0
    exact h0
  -- CORA's result: both rows of `P_` keep their direction, offsets `1 - 0`
  refine ⟨⟨2, P_.A, fun i => P_.b i - S_.b 0, 0, Fin.elim0, Fin.elim0⟩, ?_, ?_, ?_⟩
  · simp [HPolytope.minkDiff1DCora, hP, hS, P_, S_]
  · refine ⟨fun i => ?_, fun i => i.elim0⟩
    fin_cases i <;> simp [P_, S_]
  · -- `x + min 0 (-2 - x)` lies below `-1` for every `x`: the difference is empty
    refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    have hy : (fun _ => min 0 (-2 - x 0) : Vec ℝ 1) ∈ S_.construct := by
      refine ⟨fun i => ?_, fun i => i.elim0⟩
      fin_cases i
      simp [S_]
    have h := (hx _ hy).1 (show Fin 2 from 1)
    simp [P_] at h
    have := min_le_right (0 : ℝ) (-2 - x 0)
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
