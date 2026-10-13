module

public import CORALean.ContDynamics.NonlinDASys.Operations.CompLocalErrorCora
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# CORA's compositional linearization error ignores the coupling of the subsystems

`NonlinDASys.compLocalErrorCora` (`priv_linError_mixed_noInt_comp`, `options.index`) for
`ẋ₁ = y₁`, `0 = y₁ - y₂` (subsystem 1, `u = y₂`) and `ẋ₂ = y₂`, `0 = y₂ - x₂²` (subsystem 2),
linearized at `0` (`F = [[1, -1], [0, 1]]`, `C = I`, `D = 0`; see
`NonlinDASys.compositional_local_error_counterexample`). Subsystem 1's functions are linear, so
its Hessians are `0` and CORA's set `error{1}` is `{0}` for every `R_xyu` and whatever `Csub`,
`Fsub`: the sign of `CFsub_inv` is immaterial, this is not the sign issue. The true error of
`ẋ₁` at the consistent point `x₂ = 1`, `y = (1, 1)` is `1`: `f₁ = y₁ = 1` against the
linearization's `0`. Component 1 of `errorTotal` comes from `error{1}` alone (`index{2}.X'` has
a zero first row), so CORA's set misses it.

## References

* [1] M. Althoff. "Formal and Compositional Analysis of Power Systems using Reachable Sets".
      IEEE Transactions on Power Systems, 29(5):2270-2280, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. V-B]: subsystem 1 (`Hf = Hg = 0`): every point of CORA's error set is `0`, whatever
`R_xyu`, `Csub`, `Fsub`; the true error of `ẋ₁` at `x₂ = 1`, `y = (1, 1)` (consistent: `g = 0`)
is `1`. -/
theorem NonlinDASys.compLocalErrorCora_counterexample :
    (∀ (Csub Fsub : Mat ℝ 1 1) (R_xyu : Zonotope (Vec ℝ 3)),
      ∀ e ∈ (NonlinDASys.compLocalErrorCora (fun _ => 0) (fun _ => 0) (fun _ => 0)
        (fun _ => 0) Csub Fsub R_xyu).construct, e = 0) ∧
    -- true error of `ẋ₁ = y₁` at `x₂ = 1`, `y = (1, 1)`: `f₁ - (w₁ + Ã₁ Δx)` with `w = 0`, `Ã = 0`
    ((![1, 1] : Fin 2 → ℝ) 0 - 0 = 1 ∧
      (![(1 : ℝ), 1] 0 - ![1, 1] 1 = 0 ∧ ![(1 : ℝ), 1] 1 - (1 : ℝ) ^ 2 = 0)) := by -- --- PROOF ---
  refine ⟨fun Csub Fsub R e he => ?_, by simp, by simp, by simp⟩
  obtain ⟨β, -, rfl⟩ := he
  ext i
  fin_cases i
  simp [NonlinDASys.compLocalErrorCora, Zonotope.quadMap, Zonotope.plus, Zonotope.mtimes,
    Interval.zonotope, ← Pi.zero_def, dotProduct, mulVec, Fin.append, Fin.addCases]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
