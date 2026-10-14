module

public import CORALean.ContDynamics.LinearSys.Theorems.FlowIci
public import CORALean.ContDynamics.LinearSys.Theorems.FlowIoi
public import CORALean.ContDynamics.LinearSys.Definitions.MulVecL
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-!
# Every classical run is a Carathéodory one

A two-sided derivative at every point of `T` is enough for the fundamental
theorem of calculus to give the integral equation outright, at every `t ∈ T` —
no exponential substitution needed, unlike `variation_of_constants`'s closed
form. `T` convex and containing `0`, and `U` bounded, are what a window
`[0, t] ⊆ T` and its integrability cost; nothing else is added.

`u`'s measurability is `flow_Ici`'s pin `u = derivWithin x (Ici ·) · - A x`,
unconditionally measurable, off at most `T`'s greatest element — one point.
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-September-2026
-- Last update:   10-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar MeasureTheory intervalIntegral

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Convexity puts the window a flow at `t` needs, from either side of `0`, inside `T`. -/
theorem aux_uIcc_subset {T : Set ℝ} (hTconv : Convex ℝ T) {t : ℝ} (h0T : (0:ℝ) ∈ T)
    (htT : t ∈ T) : Set.uIcc 0 t ⊆ T := by
  rcases le_total 0 t with h | h
  · rw [Set.uIcc_of_le h]; exact hTconv.ordConnected.out h0T htT
  · rw [Set.uIcc_of_ge h]; exact hTconv.ordConnected.out htT h0T

/-- `u` restricted to `T` agrees, off at most `T`'s greatest element, with the
unconditionally measurable `derivWithin x (Ici ·) · - A x`; that one point is
null, so the restriction carries no cost. -/
theorem aux_aestronglyMeasurable_input {sys : LinearSys 𝕋 n} {T : Set ℝ} {R₀ U : S n}
    {x u : ℝ → Vec ℝ n} (traj : sys.CanonicalClassicalTrajectory T R₀ U x u) (hTconv : Convex ℝ T) :
    AEStronglyMeasurable u (volume.restrict T) := by -- --- PROOF ---
  have hTm : MeasurableSet T := hTconv.ordConnected.measurableSet
  have hxcont : ContinuousOn x T := fun t ht => (traj.flow t ht).continuousWithinAt
  set F : ℝ → Vec ℝ n := fun s => derivWithin x (Set.Ici s) s - toRealMat sys.A *ᵥ x s with hF
  -- `T`'s greatest element, if it has one, is the only point `flow_Ici` cannot reach
  set Tbad : Set ℝ := {m | m ∈ T ∧ IsGreatest T m} with hTbaddef
  have hTbadsub : Tbad.Subsingleton := fun a ha b hb => ha.2.unique hb.2
  have hTbad0 : volume Tbad = 0 := hTbadsub.measure_zero volume
  have hagree : ∀ s ∈ T \ Tbad, F s = u s := by
    rintro s ⟨hsT, hsbad⟩
    have hnot : ¬ IsGreatest T s := fun h => hsbad ⟨hsT, h⟩
    obtain ⟨b, hbT, hsb⟩ : ∃ b ∈ T, s < b := by
      by_contra hcon
      exact hnot ⟨hsT, fun y hy => not_lt.mp (fun hlt => hcon ⟨y, hy, hlt⟩)⟩
    have hIcc : Set.Icc s b ⊆ T := hTconv.ordConnected.out hsT hbT
    have hderiv := (traj.flow_Ici hIcc ⟨le_refl s, hsb⟩).derivWithin (uniqueDiffWithinAt_Ici s)
    simp only [hF, hderiv, add_sub_cancel_left]
  -- the disagreement set is inside `Tbad`, hence null within `volume.restrict T`
  have heq : F =ᶠ[ae (volume.restrict T)] u := by
    have hsub : {s | ¬ F s = u s} ∩ T ⊆ Tbad := by
      rintro s ⟨hne, hsT⟩
      by_contra hbad
      exact hne (hagree s ⟨hsT, hbad⟩)
    have hle : volume.restrict T {s | ¬ F s = u s} = 0 := by
      rw [Measure.restrict_apply' hTm]
      exact measure_mono_null hsub hTbad0
    rwa [Filter.EventuallyEq, ae_iff]
  have hAxcont : ContinuousOn (fun s => toRealMat sys.A *ᵥ x s) T :=
    (mulVecL (toRealMat sys.A)).continuous.comp_continuousOn hxcont
  exact ((stronglyMeasurable_derivWithin_Ici x).aestronglyMeasurable.sub
    (hAxcont.aestronglyMeasurable hTm)).congr heq

/-- The flow's integrand, bounded on the compact window `uIcc 0 t` by `x`'s own
continuity there and `U`'s boundedness, giving `IntervalIntegrable`. -/
theorem aux_intervalIntegrable_flow {sys : LinearSys 𝕋 n} {T : Set ℝ} {R₀ U : S n}
    {x u : ℝ → Vec ℝ n} (traj : sys.CanonicalClassicalTrajectory T R₀ U x u) (hTconv : Convex ℝ T)
    (h0T : (0:ℝ) ∈ T) (hU : Bornology.IsBounded (construct U)) {t : ℝ} (htT : t ∈ T) :
    IntervalIntegrable (fun s => toRealMat sys.A *ᵥ x s + u s) volume 0 t := by -- --- PROOF ---
  have hUIcc : Set.uIcc 0 t ⊆ T := aux_uIcc_subset hTconv h0T htT
  -- `x` is continuous on `T` since `flow` gives it a within-`T` derivative at every point
  have hxcontT : ContinuousOn x T := fun s hs => (traj.flow s hs).continuousWithinAt
  have hxcont : ContinuousOn x (Set.uIcc 0 t) := hxcontT.mono hUIcc
  obtain ⟨Cx, hCx⟩ := (isCompact_uIcc (a := (0:ℝ)) (b := t)).exists_bound_of_continuousOn hxcont
  obtain ⟨Cu, hCu⟩ := hU.exists_norm_le
  have hUo : Set.uIoc (0:ℝ) t ⊆ Set.uIcc 0 t := Set.uIoc_subset_uIcc
  have hmeasU : AEStronglyMeasurable u (volume.restrict (Set.uIoc (0:ℝ) t)) :=
    (aux_aestronglyMeasurable_input traj hTconv).mono_measure
      (Measure.restrict_mono (hUo.trans hUIcc) le_rfl)
  have hAxcont : ContinuousOn (fun s => toRealMat sys.A *ᵥ x s) (Set.uIoc (0:ℝ) t) :=
    (mulVecL (toRealMat sys.A)).continuous.comp_continuousOn (hxcont.mono hUo)
  have hmeasAx : AEStronglyMeasurable (fun s => toRealMat sys.A *ᵥ x s)
      (volume.restrict (Set.uIoc (0:ℝ) t)) := hAxcont.aestronglyMeasurable measurableSet_uIoc
  have hfin : volume (Set.uIoc (0:ℝ) t) < ⊤ := by
    rcases le_total 0 t with h | h
    · rw [Set.uIoc_of_le h]; exact measure_Ioc_lt_top
    · rw [Set.uIoc_of_ge h]; exact measure_Ioc_lt_top
  -- `‖A‖ Cx + Cu` bounds the integrand on the window, giving a finite integral
  rw [intervalIntegrable_iff]
  refine ⟨hmeasAx.add hmeasU, HasFiniteIntegral.restrict_of_bounded
    (C := ‖toRealMat sys.A‖ * Cx + Cu) hfin ?_⟩
  refine (ae_restrict_iff' measurableSet_uIoc).mpr (Filter.Eventually.of_forall fun s hs => ?_)
  calc ‖toRealMat sys.A *ᵥ x s + u s‖
      ≤ ‖toRealMat sys.A *ᵥ x s‖ + ‖u s‖ := norm_add_le _ _
    _ ≤ ‖toRealMat sys.A‖ * Cx + Cu :=
        add_le_add (le_trans (Matrix.linfty_opNorm_mulVec _ _)
          (mul_le_mul_of_nonneg_left (hCx _ (hUo hs)) (norm_nonneg _)))
          (hCu _ (traj.input s (hUIcc (hUo hs))))


-- =======================================  MAIN THEOREM  ======================================= --

/-- A run with a two-sided derivative everywhere on `T` also satisfies the
integral equation, so whatever is proved of `Trajectory` holds of it. -/
theorem LinearSys.CanonicalClassicalTrajectory.trajectory {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U : S n}
    {x u : ℝ → Vec ℝ n} (traj : sys.CanonicalClassicalTrajectory T R₀ U x u) (hTconv : Convex ℝ T)
    (h0T : (0:ℝ) ∈ T) (hU : Bornology.IsBounded (construct U)) :
    sys.CanonicalTrajectory T R₀ U x u where
  init := traj.init
  input := traj.input
  meas := aux_aestronglyMeasurable_input traj hTconv
  cont := fun t ht => (traj.flow t ht).continuousWithinAt
  -- the flow's own derivative, restricted to `uIcc 0 t`, gives the FTC its continuity
  flow t htT := by
    have hUIcc : Set.uIcc 0 t ⊆ T := aux_uIcc_subset hTconv h0T htT
    have hxcontT : ContinuousOn x T := fun s hs => (traj.flow s hs).continuousWithinAt
    have hcont : ContinuousOn x (Set.uIcc 0 t) := hxcontT.mono hUIcc
    have hIccT : Set.Icc (min (0:ℝ) t) (max (0:ℝ) t) ⊆ T := hUIcc
    have hderiv : ∀ s ∈ Set.Ioo (min (0:ℝ) t) (max (0:ℝ) t),
        HasDerivWithinAt x (toRealMat sys.A *ᵥ x s + u s) (Set.Ioi s) s :=
      fun s hs => traj.flow_Ioi hIccT ⟨hs.1.le, hs.2⟩
    have hint := aux_intervalIntegrable_flow traj hTconv h0T hU htT
    have hkey := integral_eq_sub_of_hasDeriv_right hcont hderiv hint
    rw [hkey]
    abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
