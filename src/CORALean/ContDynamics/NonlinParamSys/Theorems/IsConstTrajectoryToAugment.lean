module

public import CORALean.ContDynamics.NonlinParamSys.Operations.Augment
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.InnerProductSpace.Basic

@[expose] public section

/-!
# A constant-parameter trajectory is its augmented system's

`fun t => Fin.append (x t) p` is the augmented state: its first half moves as
`x` does, its second half is the constant `p`, whose integral equation is that of
the `0` the augmented field puts there. `hZ` is what makes the initial state land in
`construct Z₀`, as `hW` does in `TrajectoryToNonlinearSys.lean`, there being no
cartesian-product class on `ContSet` to build `Z₀` from `R₀` and `P` instead.
The augmented field is the parameterized one under the linear map `v ↦ (v, 0)`,
which moves through the integral.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   18-October-2026
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n m q : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinParamSys.IsConstTrajectory.toAugment {sys : NonlinParamSys n m q} {T : Set ℝ}
    {R₀ : S n} {U : S m} {P : S q} {Z₀ : S (n + q)} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m}
    {p : Vec ℝ q} {y : ℝ → Vec ℝ sys.r} (traj : sys.IsConstTrajectory T R₀ U P x u p y)
    (hZ : ∀ v ∈ construct R₀, ∀ w ∈ construct P, Fin.append v w ∈ construct Z₀) : -- --- CONCL ---
    sys.augment.IsTrajectory T Z₀ U (fun t => Fin.append (x t) p) u y := by -- --- PROOF ---
  -- `v ↦ (v, 0)`, the linear map the parameter's zero field makes of the state's
  let L : Vec ℝ n →ₗ[ℝ] Vec ℝ (n + q) :=
    { toFun := fun v => Fin.append v 0
      map_add' := fun v w => funext fun j =>
        Fin.addCases (fun i => by simp) (fun i => by simp) j
      map_smul' := fun c v => funext fun j =>
        Fin.addCases (fun i => by simp) (fun i => by simp) j }
  set L' := LinearMap.toContinuousLinearMap L
  have hz : ∀ t, Fin.append (x t) p = L' (x t) + Fin.append 0 p := fun t => funext fun j =>
    Fin.addCases (fun i => by simp [L', L]) (fun i => by simp [L', L]) j
  -- the two halves of the augmented state read back as `x t` and `p`
  have he : (fun t => sys.augment.f (Fin.append (x t) p) (u t))
      = fun t => L' (sys.f (x t) (u t) p) := by
    funext t
    have hx : Fin.append (x t) p ∘ Fin.castAdd q = x t := funext (Fin.append_left (x t) p)
    have hp : Fin.append (x t) p ∘ Fin.natAdd n = p := funext (Fin.append_right (x t) p)
    simp only [NonlinParamSys.augment, hx, hp]
    rfl
  refine ⟨hZ (x 0) traj.init p traj.param, traj.input, ?_, fun t ht => ?_, ?_, fun t ht => ?_,
    fun t ht => ?_⟩
  · rw [he]; exact L'.continuous.comp_aestronglyMeasurable traj.meas
  · rw [he]
    exact ⟨L'.integrable_comp (traj.integrable t ht).1, L'.integrable_comp (traj.integrable t ht).2⟩
  · simp_rw [hz]
    exact (L'.continuous.comp_continuousOn traj.cont).add continuousOn_const
  -- the state's own integral equation in the first half, a constant in the second
  · rw [he, L'.intervalIntegral_comp_comm (traj.integrable t ht), hz t, hz 0, traj.flow t ht,
      map_add]
    abel
  -- the augmented output map at the stack is the parameterized one
  · have hx : Fin.append (x t) p ∘ Fin.castAdd q = x t := funext (Fin.append_left (x t) p)
    have hp : Fin.append (x t) p ∘ Fin.natAdd n = p := funext (Fin.append_right (x t) p)
    rw [traj.output t ht]
    simp only [NonlinParamSys.augment, hx, hp]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
