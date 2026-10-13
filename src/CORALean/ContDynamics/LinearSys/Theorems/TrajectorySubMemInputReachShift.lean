import CORALean.ContDynamics.LinearSys.Operations.InputReach
import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableInput
import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralConstInput
import CORALean.ContDynamics.LinearSys.Theorems.InputIntegrable
import CORALean.ContDynamics.LinearSys.Theorems.IntervalIntegrableExpSubMulVec
import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants
import CORALean.ContSet.ContSet.Theorems.IsBoundedConstruct

/-!
# A run is its free motion, a named constant input, and the rest's share

The split of `sub_mem_inputReach_recentre`, with the constant a vector `u₀` the caller
names and the rest a set `U`, rather than the centre and recentring of one set `V`: a
run whose inputs satisfy `w(s) - u₀ ∈ U` has `x(t) = e^{At} x(0) + ∫₀ᵗ e^{Aσ}dσ u₀ +
∫₀ᵗ e^{A(t-s)} (w(s) - u₀) ds`, and the last term is one admissible `U`-input's
contribution, `inputReach U t`. This is how CORA's `oneStep` takes its input [1, Sec. 3.3]: a
constant vector `u` and a set `U` beside it.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every state of a run on `[0, T]` whose inputs, less `u₀`, lie in `U`, less its free
motion and what `u₀` contributes, is one `U`-input's contribution. -/
theorem LinearSys.Trajectory.sub_mem_inputReach_shift {sys : LinearSys 𝕋 n} {T : ℝ}
    {R₀ W U : S n} {x u : ℝ → Vec ℝ n} (traj : sys.Trajectory (Set.Icc 0 T) R₀ W x u)
    (u₀ : Vec ℝ n) (hWU : ∀ v ∈ construct W, v - u₀ ∈ construct U)
    (hW : Bornology.IsBounded (construct W)) (hU : Bornology.IsBounded (construct U))
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    x t - (exp (t • toRealMat sys.A) *ᵥ x 0 + MatExp.expIntegral (toRealMat sys.A) t *ᵥ u₀)
      ∈ sys.inputReach U t := by -- --- PROOF ---
  set A := toRealMat sys.A with hA
  set uc := u₀ with huc
  have hTt : Set.Icc (0:ℝ) t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc_right ht.2
  have hvoc := traj.variation_of_constants hTt le_rfl ht.1 hW
  rw [sub_zero] at hvoc
  -- the input, less the centre, is an admissible input of `Ũ`
  have hmem₀ : ∀ s ∈ Set.Icc (0:ℝ) t, u s - uc ∈ construct U :=
    fun s hs => hWU _ (traj.input s (hTt hs))
  have hmeas₀ : AEStronglyMeasurable (fun s => u s - uc) (volume.restrict (Set.Icc 0 t)) :=
    (traj.aestronglyMeasurable_input hTt).sub aestronglyMeasurable_const
  have hint₁ := intervalIntegrable_expSub_mulVec (A := A) (c := t) (S := fun k => Set (Vec ℝ k))
    (U := ({uc} : Set (Vec ℝ n))) ht.1 Bornology.isBounded_singleton
    (fun _ _ => Set.mem_singleton uc)
    aestronglyMeasurable_const
  have hint₀ := intervalIntegrable_expSub_mulVec (A := A) (c := t) ht.1
    hU hmem₀ hmeas₀
  -- the integral splits along `u = ũ + (u - ũ)`
  have hsum : (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ u s)
      = (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ uc)
        + ∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ (u s - uc) := by
    rw [← intervalIntegral.integral_add hint₁ hint₀]
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [← Matrix.mulVec_add]
    congr 1
    abel
  refine ⟨fun s => u s - uc, hmem₀, hmeas₀, ?_⟩
  rw [hvoc, hsum, MatExp.expIntegral_constInput A uc ht.1]
  abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
