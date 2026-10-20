module

public import CORALean.ContDynamics.LinearSys.Operations.InputReach
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralMulVec

@[expose] public section

/-!
# Holding the input at one point is admissible

The one member of `inputReach` an algorithm can name: hold the input at a single `v ∈ U` for the
whole window and the contribution is `(∫₀^τ e^{As} ds) v`, the integrated exponential applied to
that point. So `(∫₀^τ e^{As} ds) '' U` sits inside `inputReach U τ`, and that image, a linear image
of a representation, is convex and compact wherever `U` is, which `inputReach` itself is not known
to be here. Every inner approximation of a continuous step in this development goes through this
inclusion for that reason. The substitution `s ↦ τ - s` maps the window to itself, which is why
`inputReach` is stated over `Icc` and no endpoint bookkeeping is needed.

## Inputs
* `sys` – linear system
* `τ` – time
* `U` – input set
* `v` – point of the input set

## Hypotheses
* `hτ` – time nonnegative
* `hv` – point lies in the input set

## Conclusion
* the integrated exponential at a held point lies in the input reach
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Holding the input at one point of `U` is admissible, and what it contributes
is the integrated exponential at that point. -/
theorem LinearSys.expIntegral_mem_inputReach (sys : LinearSys 𝕋 n) {τ : ℝ} (hτ : 0 ≤ τ)
    {U : S n} {v : Vec ℝ n} (hv : v ∈ construct U) : -- --- CONCL ---
    MatExp.expIntegral (toRealMat sys.A) τ *ᵥ v
      ∈ sys.inputReach U τ := by -- --- PROOF ---
  refine ⟨fun _ => v, fun _ _ => hv, aestronglyMeasurable_const, ?_⟩
  rw [Real.MatExp.expIntegral_mulVec (toRealMat sys.A) v hτ]
  -- the substitution `s = τ - σ`, which maps the window to itself
  have h := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := τ)
    (f := fun σ => exp (σ • toRealMat sys.A) *ᵥ v) τ
  simp only [sub_self, sub_zero] at h
  exact h.symm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
