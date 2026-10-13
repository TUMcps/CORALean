import CORALean.ContDynamics.LinearSys.Operations.PostDeltaFloat
import CORALean.ContDynamics.LinearSys.Theorems.DeltaReachFloatOuter
import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolutionFloat
import CORALean.ContDynamics.LinearSys.Theorems.TrajectorySubMemInputReachRecentre

/-!
# `postDeltaFloat` holds every difference a run spans over the step

A run of `ẋ = Ax + u`, `u(t) ∈ V`, splits at time `t` into the free motion's
difference `e^{At} x(0) - x(0)`, the constant `ũ`'s share `∫₀ᵗ e^{Aσ}dσ ũ`, and the
rest, which `sub_mem_inputReach_recentre` places in `Ũ`'s input reach at `t`. Each
lies in its summand: `deltaReachFloat_outer`, and the two input reaches at `t`
inside those at `Δt` (`inputReach_mono`, both sets holding `0`), which
`inputSolutionFloat` encloses.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic NormedSpace Matrix ContSet

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The generator-free zonotope at the stored zero holds `0`. -/
theorem aux_zero_mem_segStart :
    (0 : Vec ℝ n) ∈ (Interval.point fun _ : Fin n => (FloatOps.zero : 𝕋)).zonotope.construct := by
  have h0 := Interval.zonotope_contains _ (Interval.mem_point fun _ : Fin n => (FloatOps.zero : 𝕋))
  rwa [show RealImage.realImage (fun _ : Fin n => (FloatOps.zero : 𝕋)) = (0 : Vec ℝ n) from
    funext fun _ => toReal_zero] at h0


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every run on `[0, Δt]` from `R` under inputs in `U ⊆ V` differs from its start,
at every time of the step, by a point of `postDeltaFloat`. -/
theorem LinearSys.Trajectory.postDeltaFloat_outer {sys : LinearSys 𝕋 n} {Δt : 𝕋} {η : ℕ}
    (hΔt : 0 < toReal Δt) (hη : sys.OrderAdmissibleFloat Δt Δt η) {R V : Zonotope (Vec 𝕋 n)}
    {U : Set (Vec ℝ n)} {x u : ℝ → Vec ℝ n}
    (traj : sys.Trajectory (S := fun k => Set (Vec ℝ k)) (Set.Icc 0 (toReal Δt)) R.construct U
      x u) (hUV : U ⊆ V.construct) {t : ℝ} (ht : t ∈ Set.Icc 0 (toReal Δt)) :
    x t - x 0 ∈ (sys.postDeltaFloat Δt η R V).construct := by -- --- PROOF ---
  set A := Scalar.toRealMat sys.A with hA
  set ũ := Recentre.centre V with hũ
  -- `{ũ}` and `[0, ũ]` hold what they are built from
  have hpt : ũ ∈ (Interval.point V.c).zonotope.construct :=
    Interval.zonotope_contains _ (Interval.mem_point V.c)
  set seg := LinComb.linComb (Interval.point fun _ : Fin n => (FloatOps.zero : 𝕋)).zonotope
    (Interval.point V.c).zonotope with hseg
  have h0seg : (0 : Vec ℝ n) ∈ seg.construct := by
    refine LinComb.linComb_outer (Interval.point fun _ : Fin n => (FloatOps.zero : 𝕋)).zonotope
      (Interval.point V.c).zonotope ?_
    exact ⟨0, aux_zero_mem_segStart, ũ, hpt, 1, ⟨zero_le_one, le_rfl⟩, by simp⟩
  have hũseg : ũ ∈ seg.construct := by
    refine LinComb.linComb_outer (Interval.point fun _ : Fin n => (FloatOps.zero : 𝕋)).zonotope
      (Interval.point V.c).zonotope ?_
    exact ⟨0, aux_zero_mem_segStart, ũ, hpt, 0, ⟨le_rfl, zero_le_one⟩, by simp⟩
  -- the constant's share by `t`, inside `P̃^R([0, ũ])`
  have hconst : Real.MatExp.expIntegral A t *ᵥ ũ ∈ (sys.inputSolutionFloat Δt η seg).construct :=
    sys.inputReach_subset_inputSolutionFloat hΔt hη seg
      (sys.inputReach_mono (CompactSet.isBounded_construct seg) h0seg ht.1 ht.2
        ⟨fun _ => ũ, fun _ _ => hũseg, MeasureTheory.aestronglyMeasurable_const,
          (Real.MatExp.expIntegral_constInput A ũ ht.1).symm⟩)
  -- the rest of the input's share by `t`, inside `P^R(Ũ)`
  have hrest := sys.inputReach_subset_inputSolutionFloat hΔt hη _
    (sys.inputReach_mono (CompactSet.isBounded_construct _) (Recentre.zero_mem_recentre V) ht.1
      ht.2 (traj.sub_mem_inputReach_recentre hUV ht))
  -- the free motion's difference, inside `deltaReachFloat`
  have hhom := sys.deltaReachFloat_outer hΔt hη R traj.init ht.1 ht.2
  have hsplit : x t - x 0 = (exp (t • A) *ᵥ x 0 - x 0) + (Real.MatExp.expIntegral A t *ᵥ ũ
      + (x t - (exp (t • A) *ᵥ x 0 + Real.MatExp.expIntegral A t *ᵥ ũ))) := by abel
  rw [hsplit]
  exact Plus.plus_outer (sys.deltaReachFloat Δt η R) (sys.inputSolutionFloat Δt η seg ⊞
    sys.inputSolutionFloat Δt η (Recentre.recentre V)) (Set.add_mem_add hhom
      (Plus.plus_outer (sys.inputSolutionFloat Δt η seg)
        (sys.inputSolutionFloat Δt η (Recentre.recentre V)) (Set.add_mem_add hconst hrest)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
