module

public import CORALean.ContDynamics.NeurNetContrSys.Operations.Joint
public import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachNonlinFloat
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.AugmentNonlinFlow
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.JointMem
public import CORALean.ContDynamics.NonlinearSys.Theorems.LinReachLoopFloatOuter
public import CORALean.ContDynamics.NonlinearSys.Theorems.Restrict
public import CORALean.ContDynamics.NonlinearSys.Theorems.Shift
public import CORALean.NN.Layers.Definitions.Tracks
public import CORALean.ContSet.Zonotope.Float.Theorems.ProjectOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.ReduceOuter

@[expose] public section

/-!
# `reachClosedLoopFloat` contains every sampled run at the period boundaries

At a nonlinear plant, `reachWith_timePoint_outer`'s induction ([1, Alg. 2]) with CORA's loop in
the period: a period is a run of the augmented system (`augmentNonlin_flow`), started in the joint
set of the state set and the network's image and ended in the set of `N` steps of
`linReachLoopFloat` (`aux_linReachLoopEndFloat_outer`: the first step's end set holds the run at
`Δt`, re-anchored there it is a run of the next). The joint set holds `[x; π(x)]` for every state
`x` of the set (`joint_mem`) when the network's layers track `π`, i.e. keep the generators of the
state set in front of their image (`Layer.Tracks`), which the linear and the activation layers do.

## Inputs
* `M` – plant input dimension
* `sys` – closed-loop system
* `fm` – float Hessian model of the augmented plant
* `L` – the network's layers, composed
* `π` – controller function
* `U_ext` – external input zonotope
* `options` – reachability options of one step
* `N` – steps per period
* `enlarge` – enlargement of the error
* `fuel` – iteration bound
* `step` – linear step
* `H` – number of periods
* `X₀` – initial zonotope
* `W` – disturbance set
* `x` – plant states
* `v` – external input signal
* `w` – disturbance signal

## Hypotheses
* `hfm` – model encloses the augmented plant
* `hL` – the layers track the controller
* `hdt` – the period is `N` steps
* `traj` – closed-loop trajectory

## Conclusion
* the state at every period boundary lies in the float reachable set

## References

* [1] [N. Kochdumper, C. Schilling, M. Althoff and S. Bak. "Open- and Closed-Loop Neural Network
      Verification using Polynomial Zonotopes". arXiv preprint arXiv:2207.02715,
      2022.](../../../../../references/2022/kochdumper-arxiv-nn-polyzono.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic ContSetLike

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A run of `sys` on `[0, kΔt]` from `R` under inputs in `U` is at `kΔt` in the end set of `k`
loop steps. -/
private theorem NonlinearSys.FloatHessModel.Encloses.aux_linReachLoopEndFloat_outer
    {fm : NonlinearSys.FloatHessModel 𝕋 n m} {sys : NonlinearSys n m} (h : fm.Encloses sys)
    {U : Zonotope (Vec 𝕋 m)} {options : LinearSys.ReachFloatOptions 𝕋} {enlarge : 𝕋} {fuel : ℕ}
    {step : NonlinearSys.LinearStep} : -- --- CONCL ---
    ∀ (k : ℕ) {R : Zonotope (Vec 𝕋 n)} {err : Vec 𝕋 n} {Rend : Zonotope (Vec 𝕋 n)},
      fm.step_linReachLoopEndFloat U options enlarge fuel step k R err = some Rend →
        ∀ {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {y : ℝ → Vec ℝ sys.q},
          sys.IsTrajectory (S := ExactSet) (Set.Icc 0 ((k : ℝ) * toReal options.Δt)) R.toSet
            U.toSet x u y → x ((k : ℝ) * toReal options.Δt) ∈ Rend.toSet := by -- --- PROOF ---
  intro k
  induction k with
  | zero =>
    intro R err Rend hR x u y traj
    simp only [NonlinearSys.FloatHessModel.step_linReachLoopEndFloat, Option.some.injEq] at hR
    subst hR
    simpa using traj.init
  | succ k ih =>
    intro R err Rend hR x u y traj
    simp only [NonlinearSys.FloatHessModel.step_linReachLoopEndFloat, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at hR
    obtain ⟨⟨Rτ, Rt, err'⟩, hstep, hrest⟩ := hR
    obtain ⟨hΔt, hout⟩ := h.linReachLoopFloat_outer _ _ _ hstep
    set Δt := toReal options.Δt
    -- the first step, on its own window
    have hsub : Set.Icc 0 Δt ⊆ Set.Icc 0 (((k + 1 : ℕ) : ℝ) * Δt) := fun s hs =>
      ⟨hs.1, le_trans hs.2 (by push_cast; nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])⟩
    obtain ⟨-, hend⟩ := hout (traj.restrict hsub)
    -- the run re-anchored at `Δt`, from where the first step left it
    have hmaps : Set.MapsTo (fun s => Δt + s) (Set.Icc 0 ((k : ℝ) * Δt))
        (Set.Icc 0 (((k + 1 : ℕ) : ℝ) * Δt)) := fun s hs =>
      ⟨by linarith [hs.1], by push_cast; linarith [hs.2]⟩
    have shifted := traj.shift (R₀' := (Rt.reduce options.ρ).toSet) hmaps (hsub ⟨hΔt.le, le_rfl⟩)
      (Zonotope.reduce_outer Rt options.ρ hend)
    have key := ih hrest shifted
    simpa [add_mul, add_comm] using key


/-- The loop with any joint set `jt` that holds `[x; π(x)]` for every state of the set it is
given. -/
private theorem NeurNetContrSys.aux_reachClosedLoopFloat_outer {M : ℕ}
    (sys : NeurNetContrSys (NonlinearSys n M) 𝒵[𝕋] n)
    {fm : NonlinearSys.FloatHessModel 𝕋 (n + sys.m) sys.nExt} (hfm : fm.Encloses sys.augmentNonlin)
    {jt : Zonotope (Vec 𝕋 n) → Option (Zonotope (Vec 𝕋 (n + sys.m)))}
    {π : Vec ℝ n → Vec ℝ sys.m}
    (hjt : ∀ (X : Zonotope (Vec 𝕋 n)) (J : Zonotope (Vec 𝕋 (n + sys.m))), jt X = some J →
      ∀ x ∈ toSet X, (Fin.append x (π x) : Vec ℝ (n + sys.m)) ∈ toSet J)
    {U_ext : Zonotope (Vec 𝕋 sys.nExt)} {options : LinearSys.ReachFloatOptions 𝕋} {N : ℕ}
    {enlarge : 𝕋} {fuel : ℕ} {step : NonlinearSys.LinearStep}
    (hdt : sys.dt = (N : ℝ) * toReal options.Δt) {H : ℕ} {X₀ : Zonotope (Vec 𝕋 n)}
    {W : Set (Vec ℝ (ContDynamics.nrOfDisturbances sys.plant))}
    {x : ℝ → Vec ℝ n} {v : ℝ → Vec ℝ sys.nExt}
    {w : ℝ → Vec ℝ (ContDynamics.nrOfDisturbances sys.plant)}
    (traj : sys.IsTrajectory π H X₀ (toSet U_ext) W x v w) : -- --- CONCL ---
    ∀ i ≤ H, ∀ R, fm.reachClosedLoopFloat jt U_ext options N enlarge fuel step X₀ i = some R →
      x ((i : ℝ) * sys.dt) ∈ toSet R := by -- --- PROOF ---
  intro i
  induction i with
  | zero =>
    intro _ R hR
    simp only [NonlinearSys.FloatHessModel.reachClosedLoopFloat, Option.some.injEq] at hR
    subst hR
    simpa using traj.init
  | succ i ih =>
    intro hi R hR
    have hiH : i < H := Nat.lt_of_succ_le hi
    simp only [NonlinearSys.FloatHessModel.reachClosedLoopFloat, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at hR
    obtain ⟨Xi, hXi, J, hJ, Z, hZ, hpure⟩ := hR
    simp only [pure, Option.some.injEq] at hpure
    subst hpure
    have hend := ih hiH.le Xi hXi
    -- the period is a run of the augmented system, started in the joint set
    obtain ⟨-, haug⟩ := sys.augmentNonlin_flow (traj.flow i hiH)
    have hstart := hjt Xi J hJ _ hend
    have run0 := haug (toSet J) (by simpa using hstart)
    -- the period is `N` steps of `Δt`
    have run : sys.augmentNonlin.IsTrajectory (S := ExactSet)
        (Set.Icc 0 ((N : ℝ) * toReal options.Δt)) (toSet J) (toSet U_ext)
        (fun t => Fin.append (x ((i : ℝ) * sys.dt + t)) (π (x ((i : ℝ) * sys.dt))))
        (fun t => v ((i : ℝ) * sys.dt + t)) (fun _ => fun i => i.elim0) := by
      rw [← hdt]
      exact run0
    have hz := hfm.aux_linReachLoopEndFloat_outer N hZ run
    rw [← hdt] at hz
    have h := Zonotope.project_outer Z (Fin.castAdd sys.m) ⟨_, hz, rfl⟩
    simp only [Fin.append_left] at h
    rw [show (i : ℝ) * sys.dt + sys.dt = ((i + 1 : ℕ) : ℝ) * sys.dt by push_cast; ring] at h
    exact h


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every zero-order-hold run of `H` control periods is inside `reachClosedLoopFloat` at every
period boundary where it returns a set, the network being the composite of layers `L` that
track `π`. -/
theorem NeurNetContrSys.reachClosedLoopFloat_outer {M : ℕ}
    (sys : NeurNetContrSys (NonlinearSys n M) 𝒵[𝕋] n)
    {fm : NonlinearSys.FloatHessModel 𝕋 (n + sys.m) sys.nExt} (hfm : fm.Encloses sys.augmentNonlin)
    {L : Layer 𝒵[𝕋] n sys.m} {π : Vec ℝ n → Vec ℝ sys.m} (hL : L.Tracks π)
    {U_ext : Zonotope (Vec 𝕋 sys.nExt)} {options : LinearSys.ReachFloatOptions 𝕋} {N : ℕ}
    {enlarge : 𝕋} {fuel : ℕ} {step : NonlinearSys.LinearStep}
    (hdt : sys.dt = (N : ℝ) * toReal options.Δt) {H : ℕ} {X₀ : Zonotope (Vec 𝕋 n)}
    {W : Set (Vec ℝ (ContDynamics.nrOfDisturbances sys.plant))}
    {x : ℝ → Vec ℝ n} {v : ℝ → Vec ℝ sys.nExt}
    {w : ℝ → Vec ℝ (ContDynamics.nrOfDisturbances sys.plant)}
    (traj : sys.IsTrajectory π H X₀ (toSet U_ext) W x v w) : -- --- CONCL ---
    ∀ i ≤ H, ∀ R, fm.reachClosedLoopFloat (NeurNetContrSys.joint L.enclose) U_ext options N enlarge
      fuel step X₀ i = some R → x ((i : ℝ) * sys.dt) ∈ toSet R := by -- --- PROOF ---
  exact NeurNetContrSys.aux_reachClosedLoopFloat_outer sys hfm
    (fun X J hJ _ hx => NeurNetContrSys.joint_mem hL X J hJ _ hx) hdt traj

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
