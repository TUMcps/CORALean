module

public import CORALean.ContDynamics.NonlinearSys.Definitions.IsInnerMinkDiffCert
public import CORALean.ContDynamics.NonlinearSys.Operations.InnerMinkDiffStep
public import CORALean.ContDynamics.NonlinearSys.Theorems.SubMemInputSolution
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralConstInput
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.MulExpIntegralEq
public import CORALean.ContSet.Conversion.Real.Instances

@[expose] public section

/-!
# The remainder certificate gives one step of the inner algorithm what it needs

The representation (21) a step of [1, Alg. 1] relies on, from what the remainder loop of
lines 10-13 is there to establish: when `R̂_err(L̂)` is (13) at the enlarged remainder `L̂`
(`inputSolution Δt η L̂`), `L̂` an `AbstractionError` certificate for the linearization `A` at
`x*` on a region `R` that the solutions from `X` do not leave over `[0, Δt]`, every solution
satisfies `x(Δt) - (x* + e^{AΔt}(x(0) - x*) + R_con(Δt)) ∈ R̂_err(L̂)`
(`IsTrajectory.sub_mem_inputSolution`, with `e^{AΔt}x(0) + ∫ e^{A(Δt-s)}(w - Ax*) ds` rewritten
about `x*` by `A ∫₀^Δt e^{As} ds = e^{AΔt} - I`). With [1, Prop. 1]'s other hypotheses, passed
through, that is `IsInnerMinkDiffCert`.

What stays assumed is what conservative linearization assumes: the confinement `hconf`, which
the box (25) of line 12 is meant to provide, and the properties of `L̂` and of (13) at it.

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

open CORALean.Real
open ContSet Matrix NormedSpace Scalar Set

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [OfInterval S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 1]: a remainder `L̂` certified on a region the solutions keep to gives the step
from `X` [1, Prop. 1]'s hypotheses, (21) among them. -/
theorem NonlinearSys.IsInnerMinkDiffCert.of_abstractionError [Mtimes ℐ S]
    (ops : NonlinearSys.InnerMinkDiffOps n (S n)) (sys : NonlinearSys n m) (u₀ : Vec ℝ m)
    (U : S m) (hu₀ : u₀ ∈ construct U) {Δt : ℝ} (hΔt : 0 < Δt) (μ : ℝ) (fuel η : ℕ)
    (herr : ∀ A L, ops.err Δt A L = construct ((NonlinearSys.linearize A).inputSolution Δt η L))
    {X : Set (Vec ℝ n)} {st : NonlinearSys.InnerMinkDiffState n (S n)}
    (h : NonlinearSys.innerMinkDiffStep ops (fun x => sys.f x u₀) Δt μ fuel X = some st)
    {B : Mat ℝ n m} {R : Set (Vec ℝ n)}
    (cert : AbstractionError sys.f st.A B st.xstar u₀ R (construct U) st.Lhat)
    (hconf : ∀ x₀ ∈ X, ∀ x : ℝ → Vec ℝ n, x 0 = x₀ →
      (∀ t ∈ Icc 0 Δt, HasDerivWithinAt x (sys.f (x t) u₀) (Icc 0 Δt) t) →
      ∀ t ∈ Icc 0 Δt, x t ∈ R)
    (hε : ‖Δt • st.A‖ / ((η : ℝ) + 2) < 1)
    (hconv : Convex ℝ (construct st.Lhat)) (hclosed : IsClosed (construct st.Lhat))
    (hbdd : Bornology.IsBounded (construct st.Lhat))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder st.A Δt η) st.Lhat)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder st.A Δt η) st.Lhat)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder st.A Δt η) st.Lhat)))
    (hEc : IsCompact st.Rerr) (hEcv : Convex ℝ st.Rerr) (hEne : st.Rerr.Nonempty)
    (hEs : ∀ e ∈ st.Rerr, (2 : ℝ) • st.c - e ∈ st.Rerr)
    {Ω : Set (Vec ℝ n)} {K : NNReal} (hLip : LipschitzOnWith K (fun x => sys.f x u₀) Ω)
    (hex : ∀ x₀ ∈ X, ∃ x : ℝ → Vec ℝ n, x 0 = x₀ ∧ ∀ t ∈ Icc 0 Δt,
      x t ∈ Ω ∧ HasDerivWithinAt x (sys.f (x t) u₀) (Icc 0 Δt) t) :
    NonlinearSys.IsInnerMinkDiffCert sys u₀ Δt X st := by -- --- PROOF ---
  -- what lines 5, 7 and 14 computed
  have hst : st.w = sys.f st.xstar u₀ ∧
      st.Rcon = (∫ θ in (0:ℝ)..Δt, exp ((Δt - θ) • st.A) *ᵥ st.w) ∧
      st.Rerr = ops.err Δt st.A st.Lhat := by
    unfold NonlinearSys.innerMinkDiffStep at h
    obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨rfl, rfl, rfl⟩
  refine ⟨hEc, hEcv, hEne, hEs, ⟨Ω, K, hLip, hex⟩, fun x₀ hx₀ x hx0 hder => ?_⟩
  -- the solution as a run from the point interval at `x₀`
  have traj : sys.IsTrajectory (Icc 0 Δt) (OfInterval.ofInterval (⟨x₀, x₀⟩ : Interval (Vec ℝ n)))
      U x fun _ => u₀ :=
    ⟨OfInterval.ofInterval_outer _ (by rw [hx0]; exact fun _ => ⟨le_rfl, le_rfl⟩),
      fun _ _ => hu₀, hder⟩
  have hs := traj.sub_mem_inputSolution cert (hconf x₀ hx₀ x hx0 hder) hΔt η hε hconv hclosed
    hbdd hRconv hRclosed hRbdd
  rw [hst.2.2, herr]
  -- (21) about `x*`: `e^{AΔt}x₀ + ∫ e^{A(Δt-s)}(w - Ax*) ds = x* + e^{AΔt}(x₀ - x*) + R_con`
  set A := st.A
  set EI := MatExp.expIntegral A Δt
  have hcomm : EI * A = A * EI :=
    (Commute.tsum_right A fun i => ((Commute.refl A).pow_right i).smul_right _).symm.eq
  have hEIA : EI *ᵥ (A *ᵥ st.xstar) = exp (Δt • A) *ᵥ st.xstar - st.xstar := by
    rw [Matrix.mulVec_mulVec, hcomm, MatExp.mul_expIntegral, Matrix.sub_mulVec,
      Matrix.one_mulVec]
  have hv : exp (Δt • A) *ᵥ x 0 + ∫ s in (0:ℝ)..Δt, exp ((Δt - s) • A) *ᵥ
      (sys.f st.xstar u₀ - A *ᵥ st.xstar + B *ᵥ (u₀ - u₀)) =
      st.xstar + exp (Δt • A) *ᵥ (x₀ - st.xstar) + st.Rcon := by
    rw [hst.2.1, Real.MatExp.expIntegral_constInput _ _ hΔt.le,
      Real.MatExp.expIntegral_constInput _ _ hΔt.le, hst.1, sub_self, Matrix.mulVec_zero,
      add_zero, Matrix.mulVec_sub, hEIA, hx0, Matrix.mulVec_sub]
    abel
  rw [← hv]
  exact hs

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
