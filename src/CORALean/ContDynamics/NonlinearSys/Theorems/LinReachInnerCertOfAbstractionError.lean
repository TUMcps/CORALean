module

public import CORALean.ContDynamics.NonlinearSys.Definitions.IsLinReachInnerCert
public import CORALean.ContDynamics.NonlinearSys.Operations.LinReachInner
public import CORALean.ContDynamics.NonlinearSys.Theorems.AbstractionErrorExistsNormLe
public import CORALean.ContDynamics.NonlinearSys.Theorems.IsTrajectoryOfHasDerivWithinAtOfNormLe
public import CORALean.ContDynamics.NonlinearSys.Theorems.SubMemInputSolution
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralConstInput
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.MulExpIntegralEq
public import CORALean.ContSet.Conversion.Real.Instances
public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.InputRemainderSet

@[expose] public section

/-!
# The abstraction error certificate gives CORA's inner step what it needs

The representation (21) of CORA's `contDynamics/linReachInner.m`, from what its error loop
establishes: when `Rerror` is `particularSolution_timeVarying` of `VerrorDyn`
(`inputSolution Δt η VerrorDyn`), `VerrorDyn` an `AbstractionError` certificate for `A` at `p`
on a region `R` the solutions from `Rinit` do not leave over `[0, Δt]` (CORA's `Rmax`), every
solution satisfies `x(Δt) - (p + e^{AΔt}(x(0) - p) + Rcon) ∈ Rerror`. With [1, Prop. 1]'s other
hypotheses that is `IsLinReachInnerCert`, as in `IsInnerMinkDiffCert.of_abstractionError`. Still
assumed: the confinement `hconf` and the properties of `VerrorDyn` and `Rerror`.

## Inputs
* `ops` – set operations
* `sys` – system
* `u₀` – constant input
* `U` – input set
* `Δt` – step size
* `fuel` – bound for error loop
* `η` – Taylor terms
* `X` – start set
* `e` – abstraction error guess
* `B` – input matrix
* `R` – confinement region
* `Ω` – Lipschitz region
* `K` – Lipschitz constant

## Hypotheses
* `hu₀` – input in input set
* `hΔt` – step size positive
* `herr` – operations compute the input solution
* `hconf` – solutions stay in region
* `hLip` – field Lipschitz on region
* `hex` – solutions exist from every start

## Conclusion
* the step satisfies the inner-step certificate

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
    (ops : NonlinearSys.LinReachInnerOps n (S n)) (sys : NonlinearSys n m) (u₀ : Vec ℝ m) (U : S m)
    (hu₀ : u₀ ∈ construct U) {Δt : ℝ} (hΔt : 0 < Δt) (fuel η : ℕ)
    (herr : ∀ A L, ops.inputSol Δt A L =
      construct ((NonlinearSys.linearize A).inputSolution Δt η L)) {X : Set (Vec ℝ n)} {e : Vec ℝ n}
    {B : Mat ℝ n m} {R : Set (Vec ℝ n)} (hconf : ∀ x₀ ∈ X, ∀ x : ℝ → Vec ℝ n, x 0 = x₀ →
      (∀ t ∈ Icc 0 Δt, HasDerivWithinAt x (sys.f (x t) u₀) (Icc 0 Δt) t) →
      ∀ t ∈ Icc 0 Δt, x t ∈ R) {Ω : Set (Vec ℝ n)} {K : NNReal}
    (hLip : LipschitzOnWith K (fun x => sys.f x u₀) Ω)
    (hex : ∀ x₀ ∈ X, ∃ x : ℝ → Vec ℝ n, x 0 = x₀ ∧ ∀ t ∈ Icc 0 Δt,
      x t ∈ Ω ∧ HasDerivWithinAt x (sys.f (x t) u₀) (Icc 0 Δt) t) : -- --- CONCL ---
    ∀ o ∈ NonlinearSys.linReachInner ops (fun x => sys.f x u₀) Δt fuel X e, ∀ st ∈ o,
      AbstractionError sys.f st.A B st.p u₀ R (construct U) st.VerrorDyn →
      ‖Δt • st.A‖ / ((η : ℝ) + 2) < 1 →
      Convex ℝ (construct st.VerrorDyn) →
      IsClosed (construct st.VerrorDyn) →
      Bornology.IsBounded (construct st.VerrorDyn) →
      Convex ℝ (MatExp.inputRemainderSet st.A Δt η st.VerrorDyn) →
      IsClosed (MatExp.inputRemainderSet st.A Δt η st.VerrorDyn) →
      Bornology.IsBounded
        (MatExp.inputRemainderSet st.A Δt η st.VerrorDyn) →
      IsCompact st.Rerror →
      Convex ℝ st.Rerror →
      st.Rerror.Nonempty →
      (∀ e ∈ st.Rerror, -e ∈ st.Rerror) →
      NonlinearSys.IsLinReachInnerCert sys u₀ Δt X st := by -- --- PROOF ---
  intro o (h : NonlinearSys.linReachInner ops (fun x => sys.f x u₀) Δt fuel X e = some o) st (hso :
      o = some st) cert hε hconv hclosed hbdd hRconv hRclosed hRbdd hEc hEcv hEne hEs
  subst hso
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
  -- the solution as a run from the point interval at `x₀`, its field bounded by the certificate
  obtain ⟨C, hC⟩ := cert.exists_norm_le hbdd isCompact_Icc
    (fun t ht => (hder t ht).continuousWithinAt) (hconf x₀ hx₀ x hx0 hder) hu₀
  have traj : sys.IsTrajectory (Icc 0 Δt) (OfInterval.ofInterval (⟨x₀, x₀⟩ : Interval (Vec ℝ n)))
      U x (fun _ => u₀) (fun t => sys.g (x t) u₀) :=
    .of_hasDerivWithinAt_of_norm_le (convex_Icc 0 Δt) ⟨le_rfl, hΔt.le⟩
      (OfInterval.ofInterval_outer _ (by rw [hx0]; exact fun _ => ⟨le_rfl, le_rfl⟩))
      (fun _ _ => hu₀) hder hC
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
