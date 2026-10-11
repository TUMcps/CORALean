import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral

/-!
# The support vector of [1, Sec. 4.2], as an initial state and an input sequence

The run whose state at `t_k` is the support vector `ν(Ř(t_k), ℓ)` of the inner
approximation [1, Alg. 1 (lower bounds)] bounds: the initial state of
[1]'s Eq. (19) and the piecewise-constant inputs of [1]'s Eq. (20), to be simulated
by [1]'s Eq. (18) (`heldSim`) or run in continuous time under `heldInput`.

[1]'s Eq. (20) is not used as printed. It sets
`u(j) = ν(U₀, (e^{A t_j})ᵀ ℓ) + ũ`, while (18) multiplies `u(j)` by `T` and then by
`e^{A t_{k-1-j}}` on the way to `x(k)`: the direction has to be
`(e^{A t_{k-1-j}} T)ᵀ ℓ`, with the steps counted from the end and `T` applied.
`PrintedSupportInputCounterexample` is a system on which the printed inputs miss
the support vector; the page for [1] under `references/` says more.
`ν(U₀, d) + ũ = ν(U, d)`, so `νU` is `ν(U, ·)`, and `d_j` is line 8 of
[1, Alg. 1 (lower bounds)] in closed form.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1]'s Eqs. (19)-(20), corrected: the initial state and the held inputs whose run reaches
`ν(Ř(t_k), ℓ)` at `t_k = k Δt`. -/
noncomputable def LinearSys.supportCounterexample (sys : LinearSys 𝕋 n) (Δt : ℝ)
    (ν₀ νU : (Vec ℝ n →ₗ[ℝ] ℝ) → Vec ℝ n) (ℓ : Vec ℝ n →ₗ[ℝ] ℝ) (k : ℕ) :
    Vec ℝ n × (ℕ → Vec ℝ n) :=
  let A := toRealMat sys.A
  let T := MatExp.expIntegral A Δt                                      -- (13)
  let d := fun j : ℕ => ℓ.comp (mulVecLin (exp (Δt • A) ^ j))          -- (e^{A t_j})ᵀ ℓ
  let x₀ := ν₀ (d k)                                                    -- (19)
  let u := fun j : ℕ => νU ((d (k - 1 - j)).comp (mulVecLin T))         -- (20), corrected
  (x₀, u)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
