import CORALean.ContDynamics.NonlinearSys.NonlinearSys
import CORALean.ContDynamics.NonlinearSys.Definitions.LinReachInnerState
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# What one step of CORA's `linReachInner` needs

[1, Prop. 1]'s hypotheses for the step `st` CORA's `contDynamics/linReachInner.m` computes from
the start set `X = Rinit`, in the form its proof spends them: the abstraction error `Rerror`
is convex, compact, nonempty and symmetric about the origin, which CORA's code assumes
("`center(Rerror)` is the origin") and its `Rtp = minkDiff(Rlintp, Rerror)` relies on, as
`Prop. 1` shifts by `2 cen(Rerror)`; solutions from `X` exist over `[0, Δt]` with the field
Lipschitz along them (the paper's standing assumption); and every solution from `X` satisfies
the representation (21), `x(Δt) ∈ p + e^{AΔt}(x(0) - p) + Rcon + Rerror`, which the
abstraction error loop is there to certify. `LinReachInnerCert.of_abstractionError` derives
that last field from an `AbstractionError` certificate on a region the solutions do not leave.

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
  Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
  8:2033-2038, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ} {𝓛 : Type}


-- ========================================  MAIN TYPE  ========================================= --

/-- [1, Prop. 1]'s hypotheses for the step `st` of CORA's `linReachInner` from `X`, under the
input `u₀`. -/
structure NonlinearSys.LinReachInnerCert (sys : NonlinearSys n m) (u₀ : Vec ℝ m) (Δt : ℝ)
    (X : Set (Vec ℝ n)) (st : NonlinearSys.LinReachInnerState n 𝓛) : Prop where
  compact : IsCompact st.Rerror
  convex : Convex ℝ st.Rerror
  nonempty : st.Rerror.Nonempty
  symm : ∀ e ∈ st.Rerror, -e ∈ st.Rerror
  flow : ∃ (Ω : Set (Vec ℝ n)) (K : NNReal), LipschitzOnWith K (fun x => sys.f x u₀) Ω ∧
    ∀ x₀ ∈ X, ∃ x : ℝ → Vec ℝ n, x 0 = x₀ ∧ ∀ t ∈ Set.Icc 0 Δt,
      x t ∈ Ω ∧ HasDerivWithinAt x (sys.f (x t) u₀) (Set.Icc 0 Δt) t
  err : ∀ x₀ ∈ X, ∀ x : ℝ → Vec ℝ n, x 0 = x₀ →
    (∀ t ∈ Set.Icc 0 Δt, HasDerivWithinAt x (sys.f (x t) u₀) (Set.Icc 0 Δt) t) →
    x Δt - (st.p + exp (Δt • st.A) *ᵥ (x₀ - st.p) + st.Rcon) ∈ st.Rerror

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
