module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT
public import CORALean.Global.PosDefSchurComplement
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# The nominal Luenberger observer of a descriptor system decays at rate μ

[1, Prop. 2]: for the nominal descriptor system `E x₊ = A x + B u`, `y = C x`, with `TE + NC = I`
[1, Eq. 6], the observer `x̂₊ = TA x̂ + TB u + Ḡ(y - C x̂) + N y₊` is μ-stable if `W ≻ 0`, `Y` and
`μ` satisfy `[μW ⋆; WTA - YC W] ≻ 0` Eq. 36 of [1, Prop. 2] with `Y = WḠ`: the Lyapunov function `V
= eᵀ W e` of the error `e = x - x̂` decreases, `V(e₊) < μ V(e)` for every `e ≠ 0`. As in the paper's
proof: `e₊ = (TA - ḠC) e`, and the Schur complement of the block `W` (`posDef_schur_of_fromBlocks`)
is `μW - (TA - ḠC)ᵀ W (TA - ḠC) ≻ 0`, since `WTA - YC = W(TA - ḠC)`.

## Inputs
* `E` – descriptor matrix
* `T` – decoupling matrix
* `A` – state matrix
* `N` – measurement decoupling matrix
* `Gbar` – observer gain
* `B` – input matrix
* `C` – output matrix
* `W` – Lyapunov matrix
* `μ` – decay rate
* `u` – input at this step
* `x` – state
* `x_plus` – next state
* `xhat` – estimate

## Hypotheses
* `hTN` – decoupling identity holds
* `hW` – Lyapunov matrix positive definite
* `hLMI` – block inequality positive definite
* `hE` – the descriptor step holds

## Conclusion
* the weighted estimation error shrinks by the decay rate

## References

* [1] [Y. Wang, V. Puig and G. Cembrano. "Set-membership approach and Kalman observer based on
      zonotopes for discrete-time descriptor systems". Automatica,
      2018.](../../../../../../references/2018/wang-automatica-descriptor-observer.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n nu ny : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.descriptorObserver_decay (E T A : Mat ℝ n n) (N Gbar : Mat ℝ n ny)
    (B : Mat ℝ n nu) (C : Mat ℝ ny n) (W : Mat ℝ n n) (μ : ℝ) (hTN : T * E + N * C = 1)
    (hW : W.PosDef)
    (hLMI : (fromBlocks (μ • W) (W * T * A - W * Gbar * C)ᵀ (W * T * A - W * Gbar * C) W).PosDef)
    (u : Vec ℝ nu) (x x_plus xhat : Vec ℝ n) (hE : E *ᵥ x_plus = A *ᵥ x + B *ᵥ u) : -- --- CONCL ---
    let xhat_plus := T *ᵥ (A *ᵥ xhat) + T *ᵥ (B *ᵥ u) + Gbar *ᵥ (C *ᵥ x - C *ᵥ xhat) +
      N *ᵥ (C *ᵥ x_plus)
    x - xhat ≠ 0 →
      (x_plus - xhat_plus) ⬝ᵥ (W *ᵥ (x_plus - xhat_plus)) <
        μ * ((x - xhat) ⬝ᵥ (W *ᵥ (x - xhat))) := by -- --- PROOF ---
  intro xhat_plus he
  set M : Mat ℝ n n := T * A - Gbar * C
  haveI : Invertible W := hW.isUnit.invertible
  have hWT : Wᵀ = W := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hW.isHermitian.eq
  -- the error dynamics `e₊ = (TA - ḠC) e`
  have hx : x_plus = T *ᵥ (A *ᵥ x) + T *ᵥ (B *ᵥ u) + N *ᵥ (C *ᵥ x_plus) := by
    conv_lhs => rw [← one_mulVec x_plus, ← hTN, add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hE]
    rw [mulVec_add]
  have hep : x_plus - xhat_plus = M *ᵥ (x - xhat) := by
    conv_lhs => rw [hx]
    simp only [xhat_plus, M, sub_mulVec, mulVec_sub, ← mulVec_mulVec]
    abel
  -- the Schur complement: `μW - Mᵀ W M ≻ 0`
  have hWM : W * T * A - W * Gbar * C = W * M := by
    simp only [M, Matrix.mul_sub, Matrix.mul_assoc]
  rw [hWM] at hLMI
  have hS := posDef_schur_of_fromBlocks (μ • W) (W * M)ᵀ hW
    (by rw [transpose_transpose]; exact hLMI)
  rw [transpose_transpose, transpose_mul, hWT, Matrix.mul_assoc, Matrix.mul_assoc,
    ← Matrix.mul_assoc W⁻¹, inv_mul_of_invertible, Matrix.one_mul] at hS
  have h := (posDef_iff_dotProduct_mulVec.mp hS).2 he
  rw [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, smul_eq_mul,
    ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec (x - xhat) Mᵀ, vecMul_transpose] at h
  rw [hep]
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
