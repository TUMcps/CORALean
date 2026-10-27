module

public import CORALean.ContDynamics.NonlinearSys.NonlinearSys
public import CORALean.ContDynamics.NonlinearSys.Definitions.InnerMinkDiffOps
public import CORALean.ContDynamics.NonlinearSys.Definitions.InnerMinkDiffState
public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz

@[expose] public section

/-!
# What one step of the corrected inner Minkowski-difference algorithm needs

[1, Prop. 1]'s and [1, Prop. 2]'s hypotheses for one step of the corrected [1, Alg. 1] from
`X = R̂(t_k)`, as their proofs spend them. `R̂_err(L̂)` is convex, compact, nonempty and symmetric
about `0`, as (13) makes it, and `cen` returns a center of it; `E = C ⊕ R̂_err` (22) is convex,
compact, nonempty and symmetric about line 14's `c`; `zono X` is a zonotope holding `X`.
Solutions from `X` exist over `[0, Δt]` with the field Lipschitz along them, every one satisfies
(21) at `Δt`, `x(Δt) ∈ x* + e^{AΔt}(x(0) - x*) + R_con + R̂_err`, and lies within `E` of its
chord at every `t ∈ [0, Δt]`, the representation `Prop. 2`'s proof writes.

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
      Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ} {𝓛 : Type}


-- ========================================  MAIN TYPE  ========================================= --

/-- [1, Prop. 1]'s and [1, Prop. 2]'s hypotheses for the step `st` of the corrected [1, Alg. 1]
from `X`, under the input `u₀`. -/
structure NonlinearSys.IsInnerMinkDiffCorrectedCert (sys : NonlinearSys n m) (u₀ : Vec ℝ m)
    (Δt : ℝ) (ops : NonlinearSys.InnerMinkDiffOps n 𝓛)
    (zono : Set (Vec ℝ n) → Real.Zonotope (Vec ℝ n)) (X : Set (Vec ℝ n))
    (st : NonlinearSys.InnerMinkDiffState n 𝓛) : Prop where
  -- `Prop. 1`: the abstraction error `R̂_err(L̂)` of (13)
  compact : IsCompact st.Rerr
  convex : Convex ℝ st.Rerr
  nonempty : st.Rerr.Nonempty
  symm : ∀ e ∈ st.Rerr, -e ∈ st.Rerr
  cen : ∀ e ∈ st.Rerr, (2 : ℝ) • ops.cen st.Rerr - e ∈ st.Rerr
  -- `Prop. 2`: the error `E = C ⊕ R̂_err` of (22) and the zonotope of `R̂(t_k)`
  compactE : IsCompact (st.C + st.Rerr)
  convexE : Convex ℝ (st.C + st.Rerr)
  nonemptyC : st.C.Nonempty
  symmE : ∀ e ∈ st.C + st.Rerr, (2 : ℝ) • st.c - e ∈ st.C + st.Rerr
  zono : X ⊆ (zono X).construct
  -- the solutions from `X`, (21) and the chord representation
  flow : ∃ (Ω : Set (Vec ℝ n)) (K : NNReal), LipschitzOnWith K (fun x => sys.f x u₀) Ω ∧
    ∀ x₀ ∈ X, ∃ x : ℝ → Vec ℝ n, x 0 = x₀ ∧ ∀ t ∈ Set.Icc 0 Δt,
      x t ∈ Ω ∧ HasDerivWithinAt x (sys.f (x t) u₀) (Set.Icc 0 Δt) t
  err : ∀ x₀ ∈ X, ∀ x : ℝ → Vec ℝ n, x 0 = x₀ →
    (∀ t ∈ Set.Icc 0 Δt, HasDerivWithinAt x (sys.f (x t) u₀) (Set.Icc 0 Δt) t) →
    x Δt - (st.xstar + exp (Δt • st.A) *ᵥ (x₀ - st.xstar) + st.Rcon) ∈ st.Rerr
  errτ : ∀ t ∈ Set.Icc 0 Δt, ∀ x₀ ∈ X, ∀ x : ℝ → Vec ℝ n, x 0 = x₀ →
    (∀ s ∈ Set.Icc 0 t, HasDerivWithinAt x (sys.f (x s) u₀) (Set.Icc 0 t) s) →
    x t - (x₀ + (t / Δt) •
      (st.xstar + exp (Δt • st.A) *ᵥ (x₀ - st.xstar) + st.Rcon - x₀)) ∈ st.C + st.Rerr

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
