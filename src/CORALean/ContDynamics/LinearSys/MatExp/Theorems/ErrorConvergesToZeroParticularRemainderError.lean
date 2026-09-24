import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ParticularRemainderError
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormLeOfMemParticularRemainderSet
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TendstoExpRemainderMatZero
import CORALean.Global.ErrorConvergesToZero

/-!
# `Prop. 4`: `ε_P` of eq. (22) converges to `0` with the step

[1, Prop. 4]: the error `ε_P([t_i,t_{i+1}]) = err(e^{At_i} E(Δt_i,η_i) Δt_i U)` of eq. (22)
converges to `0` for `Δt_i → 0`, and so satisfies `Assumption 1` — stated at the `i`-th step,
`t_i` arbitrary, and at `err` itself rather than at a scalar bound of it.

[1]'s proof: `Δt_i` is a multiplicative factor. Here every point of the set is within
`C·n²·‖E(Δt,η)‖·|Δt|·err(U)` of the origin, `C` the row norms of `e^{At_i}`, so
`err_le_of_forall_norm₂_le` puts `ε_P` under `√n` times that, which vanishes with `Δt` —
`|Δt|` does, and so does `E(Δt,η)` by `tendsto_expRemainderMat_zero`.

`U` bounded is the one hypothesis: it is what makes `err(U)` the input set's enclosing radius
rather than Lean's junk value for an unbounded set, and [1]'s `U` is a zonotope.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace Filter Topology

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 4]: `ε_P([t_i,t_i+Δt]) = err(e^{At_i} E(Δt,η) Δt U)` converges to `0` as `Δt → 0⁺`,
at every step start `t_i` and every order `η` — `Assumption 1` for `ε_P`. -/
theorem MatExp.errorConvergesToZero_particularRemainderError (A : Mat ℝ n n) (ti : ℝ)
    {U : Set (Vec ℝ n)} (hU : Bornology.IsBounded U) (η : ℕ) :
    ErrorConvergesToZero
      (fun Δt => MatExp.particularRemainderError A ti U Δt η) := by -- --- PROOF ---
  set C := ∑ i, ‖(fun j => (exp (ti • A)) i j)‖₂ with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun i _ => norm₂_nonneg _
  -- `ε_P` under `√n` times the pointwise radius of its set
  have hbound : ∀ Δt : ℝ, MatExp.particularRemainderError A ti U Δt η
      ≤ Real.sqrt n * (C * ((n : ℝ) ^ 2 * ‖MatExp.expRemainderMat A Δt η‖ * |Δt| * err U)) := by
    intro Δt
    have hr : 0 ≤ C * ((n : ℝ) ^ 2 * ‖MatExp.expRemainderMat A Δt η‖ * |Δt| * err U) :=
      mul_nonneg hC0 (mul_nonneg (by positivity) (err_nonneg U))
    exact err_le_of_forall_norm₂_le hr (MatExp.norm₂_le_of_mem_particularRemainderSet A ti hU Δt η)
  -- that radius vanishes with the step: `‖E(Δt,η)‖ → 0` and `|Δt| → 0`
  have hE : Tendsto (fun Δt : ℝ => ‖MatExp.expRemainderMat A Δt η‖) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [norm_zero] using (MatExp.tendsto_expRemainderMat_zero A η).norm
  have habs : Tendsto (fun Δt : ℝ => |Δt|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [abs_zero] using (continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hlim := ((((hE.const_mul ((n : ℝ) ^ 2)).mul habs).mul_const (err U)).const_mul C).const_mul
    (Real.sqrt n)
  simp only [mul_zero, zero_mul] at hlim
  exact squeeze_zero (fun Δt => err_nonneg _) hbound hlim

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
