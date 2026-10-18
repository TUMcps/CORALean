module

public import CORALean.ContDynamics.NonlinearSys.Definitions.IsLinReachInnerCert
public import CORALean.ContDynamics.NonlinearSys.Operations.LinReachInner
public import CORALean.ContDynamics.NonlinearSys.Theorems.SubMemInputSolution
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralConstInput
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.MulExpIntegralEq
public import CORALean.ContSet.Conversion.Real.Instances

@[expose] public section

/-!
# The abstraction error certificate gives CORA's inner step what it needs

The representation (21) the time-point set of CORA's `contDynamics/linReachInner.m` relies on,
from what its abstraction error loop is there to establish: when `Rerror` is
`particularSolution_timeVarying` of `VerrorDyn` (`inputSolution Δt η VerrorDyn`), and
`VerrorDyn` an `AbstractionError` certificate for the linearization `A` at `p` on a region `R`
the solutions from `Rinit` do not leave over `[0, Δt]` (CORA's `Rmax`), every solution satisfies
`x(Δt) - (p + e^{AΔt}(x(0) - p) + Rcon) ∈ Rerror` (`IsTrajectory.sub_mem_inputSolution`, with
`A ∫₀^Δt e^{As} ds = e^{AΔt} - I`). With [1, Prop. 1]'s other hypotheses, passed through, that
is `IsLinReachInnerCert`. The argument is `IsInnerMinkDiffCert.of_abstractionError`'s.

What stays assumed is what conservative linearization assumes: the confinement `hconf`, and
the properties of `VerrorDyn` and of `Rerror` at it.

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

open CORALean.Real
open ContSet Matrix NormedSpace Scalar Set

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [OfInterval S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- CORA's `linReachInner`: an abstraction error `VerrorDyn` certified on a region the solutions
keep to gives the step from `X` [1, Prop. 1]'s hypotheses, (21) among them. -/
theorem NonlinearSys.IsLinReachInnerCert.of_abstractionError [Mtimes ℐ S]
    (ops : NonlinearSys.LinReachInnerOps n (S n)) (sys : NonlinearSys n m) (u₀ : Vec ℝ m)
    (U : S m) (hu₀ : u₀ ∈ construct U) {Δt : ℝ} (hΔt : 0 < Δt) (fuel η : ℕ)
    (herr : ∀ A L, ops.inputSol Δt A L =
      construct ((NonlinearSys.linearize A).inputSolution Δt η L))
    {X : Set (Vec ℝ n)} {e : Vec ℝ n} {st : NonlinearSys.LinReachInnerState n (S n)}
    (h : NonlinearSys.linReachInner ops (fun x => sys.f x u₀) Δt fuel X e = some (some st))
    {B : Mat ℝ n m} {R : Set (Vec ℝ n)}
    (cert : AbstractionError sys.f st.A B st.p u₀ R (construct U) st.VerrorDyn)
    (hconf : ∀ x₀ ∈ X, ∀ x : ℝ → Vec ℝ n, x 0 = x₀ →
      (∀ t ∈ Icc 0 Δt, HasDerivWithinAt x (sys.f (x t) u₀) (Icc 0 Δt) t) →
      ∀ t ∈ Icc 0 Δt, x t ∈ R)
    (hε : ‖Δt • st.A‖ / ((η : ℝ) + 2) < 1)
    (hconv : Convex ℝ (construct st.VerrorDyn)) (hclosed : IsClosed (construct st.VerrorDyn))
    (hbdd : Bornology.IsBounded (construct st.VerrorDyn))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder st.A Δt η) st.VerrorDyn)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder st.A Δt η) st.VerrorDyn)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder st.A Δt η) st.VerrorDyn)))
    (hEc : IsCompact st.Rerror) (hEcv : Convex ℝ st.Rerror) (hEne : st.Rerror.Nonempty)
    (hEs : ∀ e ∈ st.Rerror, -e ∈ st.Rerror)
    {Ω : Set (Vec ℝ n)} {K : NNReal} (hLip : LipschitzOnWith K (fun x => sys.f x u₀) Ω)
    (hex : ∀ x₀ ∈ X, ∃ x : ℝ → Vec ℝ n, x 0 = x₀ ∧ ∀ t ∈ Icc 0 Δt,
      x t ∈ Ω ∧ HasDerivWithinAt x (sys.f (x t) u₀) (Icc 0 Δt) t) : -- --- STMT ---
    NonlinearSys.IsLinReachInnerCert sys u₀ Δt X st := by -- --- PROOF ---
  -- what the linearization, `particularSolution_constant` and `Rerror` computed
  have hst : st.u = sys.f st.p u₀ ∧
      st.Rcon = (∫ θ in (0:ℝ)..Δt, exp ((Δt - θ) • st.A) *ᵥ st.u) ∧
      st.Rerror = ops.inputSol Δt st.A st.VerrorDyn := by
    unfold NonlinearSys.linReachInner at h
    dsimp only at h
    split_ifs at h
    · simp at h
    obtain ⟨_, -, hr⟩ := Option.map_eq_some_iff.mp h
    obtain rfl := Option.some.inj hr
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
  -- (21) about `p`: `e^{AΔt}x₀ + ∫ e^{A(Δt-s)}(u - Ap) ds = p + e^{AΔt}(x₀ - p) + Rcon`
  set A := st.A
  set EI := MatExp.expIntegral A Δt
  have hcomm : EI * A = A * EI :=
    (Commute.tsum_right A fun i => ((Commute.refl A).pow_right i).smul_right _).symm.eq
  have hEIA : EI *ᵥ (A *ᵥ st.p) = exp (Δt • A) *ᵥ st.p - st.p := by
    rw [Matrix.mulVec_mulVec, hcomm, MatExp.mul_expIntegral, Matrix.sub_mulVec,
      Matrix.one_mulVec]
  have hv : exp (Δt • A) *ᵥ x 0 + ∫ s in (0:ℝ)..Δt, exp ((Δt - s) • A) *ᵥ
      (sys.f st.p u₀ - A *ᵥ st.p + B *ᵥ (u₀ - u₀)) =
      st.p + exp (Δt • A) *ᵥ (x₀ - st.p) + st.Rcon := by
    rw [hst.2.1, Real.MatExp.expIntegral_constInput _ _ hΔt.le,
      Real.MatExp.expIntegral_constInput _ _ hΔt.le, hst.1, sub_self, Matrix.mulVec_zero,
      add_zero, Matrix.mulVec_sub, hEIA, hx0, Matrix.mulVec_sub]
    abel
  rw [← hv]
  exact hs

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
