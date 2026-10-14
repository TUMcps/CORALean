module

public import CORALean.HybridDynamics.Operations.NonlinearResetSecondOrderBound
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# `NonlinearReset.secondOrderBoundCora`: CORA's second-order term for every output

`aux_tensorOrder2` of `hybridDynamics/@nonlinearReset/evaluate.m` builds the Hessian bound by
`arrayfun(@(i) [interval(reshape(Hx.inf(1,:,:),[n+m,n]), ...), ...], 1:2, ...)` (l. 117-121). The
lambda ignores `i` and reads output `1`, the first index of `Hx` and `Hu` being the output, so the
loop `secondOrder(i) = 0.5 * dz' * H_ * dz` (l. 132-136) gives every output the bound of output 1.
The `1:2` also fixes two outputs. Read from the source, not run.

# CORA's `nonlinearReset/evaluate` is unsound: every output gets output 1's second-order bound

For `f(x, u) = (x₁ + u, x₂²)`, `x = zonotope([0; 1], eye(2))` and `u = zonotope(0)` the centre is
`(0, 1, 0)`, `dz = (1, 1, 0)`, the Hessian of output 1 is `0` and that of output 2 is `2` at
`(x₂, x₂)`. Output 2 is `1 + 2 (x₂ - 1)`, range `[-1, 3]`, plus the second-order term. CORA's
term is `0`, so it returns `[-1, 3]`, but `x₂ = 2` gives `4`. With its own Hessian the term is `1`
and `[-2, 4]` holds `4`. Read from `evaluate.m` l. 117-121, 132-137, not run (`FINDINGS.md`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's second-order bound of output `i`: the Hessian bound of output `1` (index `0`). -/
def NonlinearReset.secondOrderBoundCora {α : Type} [Field α] {q d : Nat}
    (Habs : Fin (q + 1) → Fin d → Fin d → α) (dz : Fin d → α) (_i : Fin (q + 1)) : α :=
  NonlinearReset.secondOrderBound Habs dz 0


-- =======================================  MAIN THEOREM  ======================================= --

/-- The Hessian bounds `H_` of the witness (output 2 has `2` at `(x₂, x₂)`) and `dz = (1, 1, 0)`:
CORA's term is `0` and `[-1 - s, 3 + s]` misses `4 = f₂(0, 2)`; the output's own term is `1` and
its interval holds `4`. -/
theorem NonlinearReset.secondOrderBoundCora_counterexample (Habs : Fin 2 → Fin 3 → Fin 3 → ℝ)
    (dz : Fin 3 → ℝ) (hH : Habs = fun i a b => if i = 1 ∧ a = 1 ∧ b = 1 then 2 else 0)
    (hz : dz = ![1, 1, 0]) :
    NonlinearReset.secondOrderBoundCora Habs dz 1 = 0 ∧
      NonlinearReset.secondOrderBound Habs dz 1 = 1 ∧
      (4 : ℝ) ∈ Set.range (fun x : Set.Icc (0 : ℝ) 2 => (x : ℝ) ^ 2) ∧
      (4 : ℝ) ∉ Set.Icc (-1 - NonlinearReset.secondOrderBoundCora Habs dz 1)
        (3 + NonlinearReset.secondOrderBoundCora Habs dz 1) ∧
      (4 : ℝ) ∈ Set.Icc (-1 - NonlinearReset.secondOrderBound Habs dz 1)
        (3 + NonlinearReset.secondOrderBound Habs dz 1) := by -- --- PROOF ---
  subst hH hz
  -- the two second-order terms, by summing over the three coordinates
  have h0 : NonlinearReset.secondOrderBoundCora (q := 1) (fun (i : Fin 2) (a b : Fin 3) =>
      if i = 1 ∧ a = 1 ∧ b = 1 then (2 : ℝ) else 0) ![1, 1, 0] 1 = 0 := by
    simp [NonlinearReset.secondOrderBoundCora, NonlinearReset.secondOrderBound]
  have h1 : NonlinearReset.secondOrderBound (fun (i : Fin 2) (a b : Fin 3) =>
      if i = 1 ∧ a = 1 ∧ b = 1 then (2 : ℝ) else 0) ![1, 1, 0] 1 = 1 := by
    simp [NonlinearReset.secondOrderBound, Fin.sum_univ_three]
  refine ⟨h0, h1, ⟨⟨2, by norm_num, by norm_num⟩, by norm_num⟩, ?_, ?_⟩
  -- 4 lies above the upper end 3 + 0
  · rw [h0]; simp only [Set.mem_Icc]; intro h; linarith [h.2]
  -- 4 lies in [-2, 4]
  · rw [h1]; simp only [Set.mem_Icc]; constructor <;> linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
