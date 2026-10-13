import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral

/-!
# The equivalent discrete-time system

[1, Sec. 4.2]'s Eq. (18): `x(k + 1) = e^{AΔt} x(k) + T u(k)`, with
`T = ∫₀^{Δt} e^{Aσ} dσ` as in [1]'s Eq. (13), which `MatExp.expIntegral` is without
`[1]`'s `A⁻¹`, so a singular `A` needs no separate case. `closedForm_heldInput` is the
claim that this recursion is the continuous-time system sampled under `heldInput`.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1]'s Eq. (18): the state after `k` steps of `Δt` from `x₀` under the inputs `u`. -/
noncomputable def LinearSys.heldSim (sys : LinearSys 𝕋 n) (Δt : ℝ) (x₀ : Vec ℝ n)
    (u : ℕ → Vec ℝ n) : ℕ → Vec ℝ n
  | 0 => x₀
  | k + 1 =>
      let Φ := exp (Δt • toRealMat sys.A)                           -- e^{AΔt}
      let T := MatExp.expIntegral (toRealMat sys.A) Δt               -- (13)
      Φ *ᵥ sys.heldSim Δt x₀ u k + T *ᵥ u k                         -- (18)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
