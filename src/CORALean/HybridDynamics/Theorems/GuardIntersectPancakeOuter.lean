module

public import CORALean.ContDynamics.NonlinParamSys.Theorems.ReachUnionOuter
public import CORALean.ContDynamics.NonlinearSys.Theorems.ReachUnionOuter
public import CORALean.ContDynamics.NonlinParamSys.Theorems.IsConstTrajectoryOfHasDerivWithinAt
public import CORALean.ContDynamics.NonlinearSys.Theorems.IsTrajectoryHasDerivWithinAt
public import CORALean.ContDynamics.NonlinearSys.Theorems.Reparametrize
public import CORALean.ContDynamics.NonlinearSys.Theorems.Shift
public import CORALean.ContSet.ContSet.Theorems.Basic
public import CORALean.ContSet.ContSet.Theorems.ProjectOnHyperplaneOuter
public import CORALean.HybridDynamics.Operations.GuardIntersectPancake

@[expose] public section

/-!
# A run's guard hit is in the pancake guard intersection

The guarantee of CORA's `guardIntersect_pancake` [1] for a run with a continuous field. Time
scaling cannot reach the guard (`g → 0` there, so the scaled clock diverges at the hit), and the
proof is where that is paid. With `τ(t_f) = tScaled` and the run strictly on the invariant side up
to `t_f`, the run before `t_f` is a constant-parameter run of the scaled system
(`NonlinearSys.reparametrize`), so `x(t_f)` is in the scaled reach set; the jump holds `x(t_f + s)`
for `s ≤ δ`, and the projection fixes a point of the hyperplane. Disclosed: the scaled horizon must
reach `t_f` (`hclock`) and the hit must fall in the jump window (`ht`); these are CORA's run-time
checks, and where they fail CORA throws `Pancake approach failed!` or misses the hit.

## Inputs
* `sys` – nonlinear system
* `scaled` – time-scaled system
* `nv` – guard normal
* `d` – guard offset
* `R₀` – initial set
* `tScaled` – scaled final time
* `δ` – jump step
* `optionsScaled` – options of the scaled reach
* `optionsJump` – options of the jump reach
* `p` – parameter value
* `T` – horizon
* `x` – trajectory
* `u` – input trajectory
* `y` – output trajectory
* `tf` – time before the hit
* `t` – hit time

## Hypotheses
* `hsc` – scaled system is the pancake scaling
* `hU` – input sets agree
* `hp` – parameter lies in the parameter set
* `hp0` – parameter positive
* `traj` – the curves are a trajectory from the initial set
* `hf` – right-hand side continuous along the trajectory
* `htf` – time nonnegative
* `hδ` – jump step nonnegative
* `htfT` – jump window within the horizon
* `hpos` – trajectory strictly on the invariant side
* `hclock` – scaled clock reaches the scaled horizon
* `ht` – hit time within the jump window
* `hhit` – state is on the guard hyperplane

## Conclusion
* every result set contains the guard hit

## References

* [1] `hybridDynamics/@location/guardIntersect_pancake.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Set

variable {S Rg : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (Rg n) (Vec ℝ n)]
variable {m n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [OfInterval S] [Mtimes ℐ S] [∀ n, Contains (Rg n) (S n)]
variable [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)]
variable [∀ n, OfPoint (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A guard point `x t`, `t ∈ [t_f, t_f + δ]`, of a run strictly inside until `t_f`, is in the
set. -/
theorem NonlinearSys.WithSteps.guardIntersectPancake_outer (sys : NonlinearSys.WithSteps S Rg m n)
    (scaled : NonlinParamSys.WithSteps S Rg m 1 n) (nv : Vec ℝ n) (d : ℝ) (R₀ : S n) (tScaled δ : ℝ)
    (optionsScaled optionsJump : LinearSys.ReachOptions ℝ)
    (hsc : scaled.sys = sys.sys.pancakeScaled nv d) (hU : construct scaled.aug.U = construct sys.U)
    {p : Vec ℝ 1} (hp : p ∈ construct scaled.P) (hp0 : 0 < p 0) {T : ℝ} {x : ℝ → Vec ℝ n}
    {u : ℝ → Vec ℝ m} {y : ℝ → Vec ℝ sys.sys.q}
    (traj : sys.sys.IsTrajectory (Icc 0 T) R₀ sys.U x u y)
    (hf : ContinuousOn (fun s => sys.sys.f (x s) (u s)) (Icc 0 T)) {tf : ℝ} (htf : 0 ≤ tf)
    (hδ : 0 ≤ δ) (htfT : tf + δ ≤ T) (hpos : ∀ s ∈ Icc 0 tf, 0 < nv ⬝ᵥ x s - d)
    (hclock : ∫ r in (0 : ℝ)..tf, ((nv ⬝ᵥ x r - d) / p 0)⁻¹ = tScaled) {t : ℝ}
    (ht : t ∈ Icc tf (tf + δ)) (hhit : nv ⬝ᵥ x t = d) :
    ∀ Z ∈ sys.guardIntersectPancake scaled nv d R₀ tScaled δ optionsScaled optionsJump,
      x t ∈ construct Z := by -- --- PROOF ---
  intro Z (hZ : sys.guardIntersectPancake scaled nv d R₀ tScaled δ optionsScaled optionsJump = some
      Z)
  -- the run before `t_f`, reparametrized: a constant-parameter run of the scaled system
  have hgc : Continuous (fun z : Vec ℝ n => (nv ⬝ᵥ z - d) / p 0) := by
    unfold dotProduct; fun_prop
  have htfT' : tf ≤ T := by linarith [ht.1, ht.2]
  have hx : ∀ s ∈ Icc 0 T, HasDerivWithinAt x (sys.sys.f (x s) (u s)) (Icc 0 T) s :=
    fun s hs => traj.hasDerivWithinAt ⟨le_rfl, htf.trans htfT'⟩ hf hs
  obtain ⟨σ, hσ0, hσT, hmaps, hσd, hy, -⟩ := sys.sys.reparametrize tf htf x u
    (fun z => (nv ⬝ᵥ z - d) / p 0)
    (fun s hs => (hx s ⟨hs.1, hs.2.trans htfT'⟩).mono (Icc_subset_Icc_right htfT'))
    hgc.continuousOn (fun s hs => div_pos (hpos s hs) hp0)
  have hS0 : 0 ≤ tScaled := by
    rw [← hclock]
    exact intervalIntegral.integral_nonneg htf fun r hr =>
      inv_nonneg.2 (div_pos (hpos r hr) hp0).le
  -- the same at the horizon `tScaled` the integral equals
  have hσT' : σ tScaled = tf := by rw [← hclock]; exact hσT
  have hmaps' : MapsTo σ (Icc 0 tScaled) (Icc 0 tf) := by rw [← hclock]; exact hmaps
  have hσc : ContinuousOn σ (Icc 0 tScaled) := by
    rw [← hclock]; exact fun s hs => (hσd s hs).continuousWithinAt
  have hy' : ∀ s ∈ Icc 0 tScaled, HasDerivWithinAt (x ∘ σ)
      (((nv ⬝ᵥ (x ∘ σ) s - d) / p 0) • sys.sys.f ((x ∘ σ) s) (u (σ s))) (Icc 0 tScaled) s := by
    rw [← hclock]; exact hy
  unfold NonlinearSys.WithSteps.guardIntersectPancake at hZ
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hZ
  obtain ⟨Rs, hRs, Rj, hRj, rfl⟩ := hZ
  -- `x(t_f)` is in the scaled reach set at the horizon
  have hmem : x tf ∈ construct Rs := by
    have h1 := scaled.reachUnion_outer ⟨R₀, 0, tScaled⟩ optionsScaled _ hRs
    have hx : x tf ∈ scaled.reachUnionExact (tScaled - 0) (construct R₀) := by
      simp only [NonlinParamSys.WithSteps.reachUnionExact, mem_iUnion, mem_setOf_eq, sub_zero]
      have hmapsT : MapsTo σ (Icc 0 tScaled) (Icc 0 T) :=
        fun s hs => ⟨(hmaps' hs).1, (hmaps' hs).2.trans htfT'⟩
      -- the scaled field along the reparametrized run, continuous, so integrable
      have hFc : ContinuousOn (fun s => scaled.sys.f ((x ∘ σ) s) ((u ∘ σ) s) p)
          (Icc 0 tScaled) := by
        rw [hsc]
        exact (hgc.comp_continuousOn (traj.cont.comp hσc hmapsT)).smul (hf.comp hσc hmapsT)
      refine ⟨tScaled, ⟨hS0, le_rfl⟩, x ∘ σ, u ∘ σ, p,
        NonlinParamSys.IsConstTrajectory.of_hasDerivWithinAt (convex_Icc 0 tScaled) ⟨le_rfl, hS0⟩
          ?_ (fun s hs => ?_) hp (fun s hs => ?_)
          (fun s hs => (hFc.mono (uIcc_subset_Icc ⟨le_rfl, hS0⟩ hs)).intervalIntegrable), ?_⟩
      · simpa [hσ0] using traj.init
      · rw [hU]; exact traj.input _ (hmapsT hs)
      · rw [hsc]; exact hy' s hs
      · simp [hσT']
    exact h1 hx
  obtain ⟨Ri, hRi, hxRi⟩ := SetUnion.mem_construct.mp hmem
  -- the jump from the member `Ri` is somewhere in the list
  have hmap : ∀ (l : List (S n)) (r : List (SetUnion (S n))),
      l.mapM (fun Ri => sys.reachUnion ⟨Ri, 0, δ⟩ optionsJump) = some r → ∀ a ∈ l,
      ∃ J, sys.reachUnion ⟨a, 0, δ⟩ optionsJump = some J ∧ J ∈ r := by
    intro l
    induction l with
    | nil => intro r _ a ha; simp at ha
    | cons b l ih =>
      intro r h a ha
      -- unfold the head step, then the tail, and conclude by the induction hypothesis
      rw [List.mapM_cons] at h
      cases hJ : sys.reachUnion ⟨b, 0, δ⟩ optionsJump with
      | none => simp [hJ] at h
      | some J =>
        cases hl : List.mapM (fun Ri => sys.reachUnion ⟨Ri, 0, δ⟩ optionsJump) l with
        | none => simp [hJ, hl] at h
        | some rs =>
          simp [hJ, hl] at h
          subst h
          rcases List.mem_cons.mp ha with rfl | ha
          · exact ⟨J, hJ, List.mem_cons_self⟩
          · obtain ⟨J', hJ', hm⟩ := ih rs hl a ha
            exact ⟨J', hJ', List.mem_cons_of_mem _ hm⟩
  obtain ⟨J, hJ, hJm⟩ := hmap _ _ hRj Ri hRi
  -- the shifted run is a run of the original system from `Ri` over `[0, δ]`
  have hxJ : x t ∈ construct J := by
    have h2 := sys.reachUnion_outer ⟨Ri, 0, δ⟩ optionsJump _ hJ
    refine h2 ?_
    simp only [NonlinearSys.WithSteps.reachUnionExact, mem_iUnion, NonlinearSys.reachSetExact,
      mem_setOf_eq, sub_zero]
    have traj' : sys.sys.IsTrajectory (S := 𝒮) (Icc 0 T) (construct R₀) (construct sys.U) x u y :=
      ⟨traj.init, traj.input, traj.meas, traj.integrable, traj.cont, traj.flow, traj.output⟩
    have hxtf : x tf ∈ construct Ri := by simpa [hσT'] using hxRi
    exact ⟨t - tf, ⟨by linarith [ht.1], by linarith [ht.2]⟩, fun s => x (tf + s),
      fun s => u (tf + s), { traj'.shift (R₀' := construct Ri) (T' := Icc 0 δ)
        (fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩) ⟨htf, htfT'⟩ hxtf with
          output := fun _ _ => rfl }, by simp⟩
  -- a point of the hyperplane is fixed by the projection
  obtain ⟨Rk, hRk, hxRk⟩ := SetUnion.mem_construct.mp hxJ
  refine SetUnion.mem_construct.mpr
    ⟨_, List.mem_map.mpr ⟨Rk, List.mem_flatMap.mpr ⟨J, hJm, hRk⟩, rfl⟩, ?_⟩
  have hfix : x t - (((Real.sqrt (nv ⬝ᵥ nv))⁻¹ • nv) ⬝ᵥ x t - d / Real.sqrt (nv ⬝ᵥ nv)) •
      ((Real.sqrt (nv ⬝ᵥ nv))⁻¹ • nv) ∈ construct (ContSet.projectOnHyperplane Rk
        ((Real.sqrt (nv ⬝ᵥ nv))⁻¹ • nv) (d / Real.sqrt (nv ⬝ᵥ nv))) :=
    ContSet.projectOnHyperplane_outer Rk _ _ ⟨x t, hxRk, rfl⟩
  have h0 : ((Real.sqrt (nv ⬝ᵥ nv))⁻¹ • nv) ⬝ᵥ x t - d / Real.sqrt (nv ⬝ᵥ nv) = 0 := by
    rw [smul_dotProduct, hhit, smul_eq_mul, div_eq_mul_inv]; ring
  rwa [h0, zero_smul, sub_zero] at hfix

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
