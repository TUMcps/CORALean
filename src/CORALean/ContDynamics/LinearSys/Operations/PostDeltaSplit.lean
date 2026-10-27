module

public import CORALean.ContDynamics.LinearSys.Operations.DeltaReach
public import CORALean.ContDynamics.LinearSys.Operations.InputSolution
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ConstCorrectionMatrix
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral

@[expose] public section

/-!
# `postΔ` at an input set that misses the origin

[1, Sec. 4.1], line 6 of Alg. 1: `R∆(τs) = post∆(R(ts), Ψ(τs), A)`, a slight modification of the
standard techniques [Althoff's thesis, Chap. 3.2], returning the set of state differences instead
of the set of states. `Ψ(τs)` is `w ⊕ B ⊗ U ⊕ ½ sq(D, R(τs) × U) ⊕ L(τs)` (line 9), which holds the
constant `w` and so need not hold the origin; the standard technique splits it into a constant `ũ`
and a set `Ũ` that does, and encloses each share. `postDeltaSplit` is that: `deltaReach`'s
homogeneous differences, the constant's share (`∫₀ʳ e^{Aσ}dσ` applied to the segment `Sg` from the
origin to `ũ`, widened by the correction matrix `F̃` applied to `P ∋ ũ`) and `inputSolution` at `Ũ`.
At `0 ∈ Ψ` the split is `ũ = 0`, `Ũ = Ψ`, and `postDelta` is the shorter form.

## Inputs
* `sys` – linear system
* `r` – step length
* `η` – Taylor order
* `R₀` – initial set
* `Sg` – segment from the origin to the constant input
* `P` – set holding the constant input
* `U₀` – recentered input set

## Output
* every state difference a step can span under the split input

## References

* [1] [M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative Polynomialization
      and Non-Convex Sets". Proceedings of the 16th international conference on Hybrid systems:
      computation and control,
      2013.](../../../../../references/2013/althoff-hscc-conservative-polynomialization.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Scalar ContSet

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `post∆(R(ts), Ψ(τs), A)` with `Ψ` split along `{ũ} ⊕ Ũ`: `Sg` holds the segment from the
origin to `ũ`, `P` holds `ũ`, and `U₀ = Ũ`. -/
noncomputable def LinearSys.postDeltaSplit (sys : LinearSys 𝕋 n) (r : ℝ) (η : ℕ)
    (R₀ Sg P U₀ : S n) : S n :=
  let RΔh := sys.deltaReach r η R₀                                -- the homogeneous differences
  let Pũ := Plus.plus                                             -- the constant ũ's share
    (Mtimes.mtimes (𝕄 := Mat ℝ) (MatExp.expIntegral (toRealMat sys.A) r) Sg)
    (Mtimes.mtimes (𝕄 := ℐ) (MatExp.constCorrectionMatrix (toRealMat sys.A) r η) P)
  let PŨ := sys.inputSolution r η U₀                             -- Ũ's share
  Plus.plus RΔh (Plus.plus Pũ PŨ)                                 -- R∆(τs)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
