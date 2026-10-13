import CORALean.ContDynamics.NonlinearSys.NonlinearSys
import CORALean.ContDynamics.NonlinearSys.Definitions.InnerMinkDiffState
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# What one step of the inner Minkowski-difference algorithm needs

[1, Prop. 1]'s hypotheses for one step of [1, Alg. 1] from the start set `X = R̂(t_k)`, in the
form its proof spends them: the abstraction error `R̂_err(L̂)` is convex, compact, nonempty and
symmetric about the centre `c` line 14 computes; solutions from `X` exist over `[0, Δt]` with
the field Lipschitz along them (the paper's standing assumption); and every solution from `X`
satisfies the representation (21), `x(Δt) ∈ x* + e^{AΔt}(x(0) - x*) + R_con(Δt) + R̂_err(L̂)`,
which is what the remainder loop of lines 10-13 is there to certify (written about `x*`, as
(10)-(12) are once `x* = 0ₙ` is undone). `InnerMinkDiffCert.of_abstractionError` derives that
last field from an `AbstractionError` certificate for `L̂` on a region the solutions do not leave.

`symm` asks for symmetry about line 14's `c = cen(C) + cen(R̂_err)`, not about `cen(R̂_err)` as
`Prop. 1` does: a nonempty bounded set symmetric about two points is invariant under the
translation by twice their difference, so for line 15 this holds only when `cen(C) = 0`.

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
  Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
  8:2033-2038, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ} {𝓛 : Type}


-- ========================================  MAIN TYPE  ========================================= --

/-- [1, Prop. 1]'s hypotheses for the step `st` of [1, Alg. 1] from `X`, under the input `u₀`. -/
structure NonlinearSys.InnerMinkDiffCert (sys : NonlinearSys n m) (u₀ : Vec ℝ m) (Δt : ℝ)
    (X : Set (Vec ℝ n)) (st : NonlinearSys.InnerMinkDiffState n 𝓛) : Prop where
  compact : IsCompact st.Rerr
  convex : Convex ℝ st.Rerr
  nonempty : st.Rerr.Nonempty
  symm : ∀ e ∈ st.Rerr, (2 : ℝ) • st.c - e ∈ st.Rerr
  flow : ∃ (Ω : Set (Vec ℝ n)) (K : NNReal), LipschitzOnWith K (fun x => sys.f x u₀) Ω ∧
    ∀ x₀ ∈ X, ∃ x : ℝ → Vec ℝ n, x 0 = x₀ ∧ ∀ t ∈ Set.Icc 0 Δt,
      x t ∈ Ω ∧ HasDerivWithinAt x (sys.f (x t) u₀) (Set.Icc 0 Δt) t
  err : ∀ x₀ ∈ X, ∀ x : ℝ → Vec ℝ n, x 0 = x₀ →
    (∀ t ∈ Set.Icc 0 Δt, HasDerivWithinAt x (sys.f (x t) u₀) (Set.Icc 0 Δt) t) →
    x Δt - (st.xstar + exp (Δt • st.A) *ᵥ (x₀ - st.xstar) + st.Rcon) ∈ st.Rerr

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
