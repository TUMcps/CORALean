module

public import CORALean.HybridDynamics.Theorems.Basic
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolutionFloat
public import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalStepFloatOuter
public import CORALean.ContDynamics.LinearSys.Theorems.IsTrajectorySubMemInputReachRecenter
public import CORALean.ContSet.ContSet.Theorems.Basic
public import CORALean.HybridDynamics.Operations.TimeIntervalStepSplitFloat
public import CORALean.HybridDynamics.Theorems.LinearEmbedding
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains

@[expose] public section

/-!
# A stay is enclosed by the split float step, wherever the input set sits

`timeInterval_outer_split` in floats. `sub_mem_inputReach_recenter` takes `x t`
apart into its free motion, the constant `ũ`'s contribution `∫₀ᵗ e^{Aσ}dσ ũ`
and one `Ũ`-input's contribution. The first is in `timeIntervalStepFloat`. The
second is an admissible input of `[0, ũ]` held over `[0, t]`, and the third an
admissible input of `Ũ`; both segments hold the origin, so `inputReach_mono`
lifts each from `t` to `r`, where `inputReach_subset_inputSolutionFloat` places
it in its float input solution.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic
open Matrix ContSet NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
variable {G : ℕ → Type} [∀ n, ContSet (G n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every state a stay passes through by time `r` lies in the split float step
from `R₀`, with no assumption on where `ℓ.inputSetFloat` sits. -/
theorem Location.IsTrajectory.timeIntervalSplitFloat_outer
    {ℓ : Location 𝒵[𝕋] G L 𝕋 n} {τ : ℝ} {x : ℝ → Vec ℝ n} {u w}
    (traj : ℓ.IsTrajectory τ x u w)
    {R₀ : Zonotope (Vec 𝕋 n)} (h₀ : x 0 ∈ construct R₀) {r : 𝕋} {η : ℕ} (hr : 0 < toReal r)
    (hη : ℓ.dynamics.OrderAdmissibleFloat r r η) {t : ℝ} (ht0 : 0 ≤ t) (htτ : t ≤ τ)
    (htr : t ≤ toReal r) : -- --- STMT ---
    x t ∈ construct (ℓ.timeIntervalStepSplitFloat r η R₀) := by -- --- PROOF ---
  set A := Scalar.toRealMat ℓ.dynamics.A with hA
  set ũ := Recenter.center ℓ.inputSetFloat with hũ
  -- `x t` less its free motion and the constant's share is one `Ũ`-input's share
  have hrest := (traj.linearSys h₀ traj.inputSetFloat_mem).sub_mem_inputReach_recenter
      (S' := 𝒵[𝕋]) (V := ℓ.inputSetFloat)
      subset_rfl
    ⟨ht0, htτ⟩
  -- `{ũ}` and `[0, ũ]` hold what they are built from
  have hpt : ũ ∈ (Interval.point ℓ.inputSetFloat.c).zonotope.construct :=
    Interval.zonotope_contains _ (Interval.mem_point ℓ.inputSetFloat.c)
  have hzero : (0 : Vec ℝ n) ∈ (Interval.point fun _ : Fin n => (zero : 𝕋)).zonotope.construct := by
    have h0 := Interval.zonotope_contains _ (Interval.mem_point fun _ : Fin n => (zero : 𝕋))
    rwa [show RealImage.realImage (fun _ : Fin n => (zero : 𝕋)) = (0 : Vec ℝ n) from
      funext fun _ => toReal_zero] at h0
  set seg := LinComb.linComb (Interval.point fun _ : Fin n => (zero : 𝕋)).zonotope
    (Interval.point ℓ.inputSetFloat.c).zonotope with hseg
  have h0seg : (0 : Vec ℝ n) ∈ seg.construct :=
    LinComb.linComb_outer (Interval.point fun _ : Fin n => (zero : 𝕋)).zonotope
      (Interval.point ℓ.inputSetFloat.c).zonotope
      ⟨0, hzero, ũ, hpt, 1, ⟨zero_le_one, le_rfl⟩, by simp⟩
  have hũseg : ũ ∈ seg.construct :=
    LinComb.linComb_outer (Interval.point fun _ : Fin n => (zero : 𝕋)).zonotope
      (Interval.point ℓ.inputSetFloat.c).zonotope
      ⟨0, hzero, ũ, hpt, 0, ⟨le_rfl, zero_le_one⟩, by simp⟩
  -- the constant `ũ` held over `[0, t]` is an admissible input of `[0, ũ]`
  have hconst : Real.MatExp.expIntegral A t *ᵥ ũ
      ∈ ℓ.dynamics.inputReach (S := 𝒵[𝕋]) seg t :=
    ⟨fun _ => ũ, fun _ _ => hũseg, aestronglyMeasurable_const,
      (Real.MatExp.expIntegral_constInput A ũ ht0).symm⟩
  have hc := ℓ.dynamics.inputReach_subset_inputSolutionFloat hr hη seg
    (ℓ.dynamics.inputReach_mono (CompactSet.isBounded_construct seg) h0seg ht0 htr hconst)
  -- the recentered input's share, lifted from `t` to `r`
  have hU := ℓ.dynamics.inputReach_subset_inputSolutionFloat hr hη
    (Recenter.recenter ℓ.inputSetFloat)
    (ℓ.dynamics.inputReach_mono (CompactSet.isBounded_construct _)
      (Recenter.zero_mem_recenter ℓ.inputSetFloat) ht0 htr hrest)
  have hH := ℓ.dynamics.timeIntervalStepFloat_outer hr hη R₀ h₀ ht0 htr
  have hx : x t = (exp (t • A) *ᵥ x 0 + Real.MatExp.expIntegral A t *ᵥ ũ)
      + (x t - (exp (t • A) *ᵥ x 0 + Real.MatExp.expIntegral A t *ᵥ ũ)) := by abel
  rw [hx]
  exact Plus.plus_outer _ _ (Set.add_mem_add
    (Plus.plus_outer _ _ (Set.add_mem_add hH hc)) hU)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
