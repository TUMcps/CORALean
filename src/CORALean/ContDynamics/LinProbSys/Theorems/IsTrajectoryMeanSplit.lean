module

public import CORALean.ContDynamics.LinProbSys.LinProbSys
public import CORALean.ContDynamics.LinearSys.Operations.Canonical
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralMulVec
public import CORALean.ContDynamics.LinearSys.Theorems.IntervalIntegrableExpSubMulVec
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Theorems.Basic
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMemIff
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact

@[expose] public section

/-!
# The mean of a run, split as CORA's input solution splits it

CORA's input set is `U + uTrans` [1]. For a `LinProbSys.IsTrajectory` with that input set, on a
`T` that holds `[0, t]`, the mean `e^{At} x₀ + ∫₀ᵗ e^{A(t-s)} B u(s) ds` at `t` is
`e^{At} x₀ + ∫₀ᵗ e^{Aσ} dσ B uTrans + w` with `w` a point `B U` reaches in `t`
(`LinearSys.inputReach` of the canonical form at `A`): the form `initReach_tp_outer` and
`initReach_ti_outer` take the mean in.

## References

* [1] `contDynamics/@linProbSys/private/priv_inputSolution.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet MeasureTheory NormedSpace CORALean.Real

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- With the input in `U + uTrans` on `[0, t]`, the mean at `t` is
`e^{At} x₀ + ∫₀ᵗ e^{Aσ} dσ B uTrans + w` for a `w` that `B U` reaches in `t`. -/
theorem LinProbSys.IsTrajectory.mean_eq_add_inputReach {sys : LinProbSys n m} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {T : Set ℝ} {X₀ : Zonotope (Vec ℝ n)}
    {U : Zonotope (Vec ℝ m)} {uTrans : Vec ℝ m} {x₀ : Vec ℝ n} {u : ℝ → Vec ℝ m}
    {x : ℝ → Ω → Vec ℝ n}
    (traj : sys.IsTrajectory (S := 𝒵) P T X₀ (U.plus (Zonotope.ofPoint uTrans)) x₀ u x) {t : ℝ}
    (h0 : 0 ≤ t) (hT : Set.Icc 0 t ⊆ T) : -- --- STMT ---
    ∃ w ∈ (LinearSys.canonical sys.A : LinearSys ℝ n).inputReach (S := 𝒵)
        (Zonotope.mtimes sys.B U) t,
      exp (t • sys.A) *ᵥ x₀ + ∫ s in (0:ℝ)..t, exp ((t - s) • sys.A) *ᵥ (sys.B *ᵥ u s)
        = exp (t • sys.A) *ᵥ x₀ + MatExp.expIntegral sys.A t *ᵥ (sys.B *ᵥ uTrans)
          + w := by -- --- PROOF ---
  set A := sys.A
  -- the input less `uTrans` is in `U`
  have hu : ∀ s ∈ Set.Icc (0:ℝ) t, u s - uTrans ∈ U.construct := fun s hs => by
    have h := traj.input s (hT hs)
    change u s ∈ (U.plus (Zonotope.ofPoint uTrans)).construct at h
    rw [← Zonotope.plus_exact] at h
    obtain ⟨a, ha, b, hb, hab⟩ := h
    rw [Zonotope.mem_ofPoint_iff] at hb
    rw [← hab, hb, add_sub_cancel_right]
    exact ha
  set v : ℝ → Vec ℝ n := fun s => sys.B *ᵥ (u s - uTrans) with hvdef
  -- the input less `uTrans`, in `B U` and measurable on `[0, t]`
  have hv : ∀ s ∈ Set.Icc (0:ℝ) t, v s ∈ construct (Zonotope.mtimes sys.B U) := fun s hs => by
    show _ ∈ (Zonotope.mtimes sys.B U).construct
    rw [← Zonotope.mtimes_exact]
    exact ⟨_, hu s hs, rfl⟩
  have hvmeas : AEStronglyMeasurable v (volume.restrict (Set.Icc 0 t)) :=
    (Continuous.comp_aestronglyMeasurable (by fun_prop : Continuous (sys.B *ᵥ ·))
      ((traj.meas.mono_measure (Measure.restrict_mono hT le_rfl)).sub
        aestronglyMeasurable_const))
  refine ⟨∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ v s, ⟨v, hv, hvmeas, rfl⟩, ?_⟩
  -- the integral splits into the constant part and the rest
  have hsplit : (fun s => exp ((t - s) • A) *ᵥ (sys.B *ᵥ u s))
      = fun s => exp ((t - s) • A) *ᵥ (sys.B *ᵥ uTrans) + exp ((t - s) • A) *ᵥ v s := by
    funext s
    simp only [hvdef, mulVec_sub, add_sub_cancel]
  have hc : IntervalIntegrable (fun s => exp ((t - s) • A) *ᵥ (sys.B *ᵥ uTrans)) volume 0 t :=
    (Continuous.matrix_mulVec (NormedSpace.exp_continuous.comp
      ((continuous_const.sub continuous_id).smul continuous_const)) continuous_const
      ).intervalIntegrable _ _
  have hw : IntervalIntegrable (fun s => exp ((t - s) • A) *ᵥ v s) volume 0 t :=
    intervalIntegrable_expSub_mulVec (S := 𝒵) h0 (Zonotope.isCompact_construct _).isBounded hv
      hvmeas
  -- the constant part is `∫₀ᵗ e^{Aσ} dσ B uTrans`
  have hconst : ∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ (sys.B *ᵥ uTrans)
      = MatExp.expIntegral A t *ᵥ (sys.B *ᵥ uTrans) := by
    rw [MatExp.expIntegral_mulVec A _ h0,
      intervalIntegral.integral_comp_sub_left (fun σ => exp (σ • A) *ᵥ (sys.B *ᵥ uTrans)) t]
    simp
  rw [hsplit, intervalIntegral.integral_add hc hw, hconst, add_assoc]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
