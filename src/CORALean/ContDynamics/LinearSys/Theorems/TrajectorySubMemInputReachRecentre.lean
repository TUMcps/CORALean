module

public import CORALean.ContDynamics.LinearSys.Operations.InputReach
public import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableInput
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralConstInput
public import CORALean.ContDynamics.LinearSys.Theorems.InputIntegrable
public import CORALean.ContDynamics.LinearSys.Theorems.IntervalIntegrableExpSubMulVec
public import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants
public import CORALean.ContSet.ContSet.Definitions.CompactSet
public import CORALean.ContSet.ContSet.Theorems.Basic

@[expose] public section

/-!
# A run is its free motion, its constant input, and a recentred input's share

[1, Alg. 3]'s split, at one run: with inputs in `U ⊆ V` and `V = ũ ⊕ Ũ` by
`Recentre`, `x(t) = e^{At} x(0) + ∫₀ᵗ e^{Aσ}dσ ũ + ∫₀ᵗ e^{A(t-s)} (u(s) - ũ) ds`,
and the last term is one admissible `Ũ`-input's contribution, `inputReach Ũ t`.
The argument `WithInputSplit.reach_outer` makes inline, named so that a float
reach can state its windows against the same three pieces.

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
variable {S' : ℕ → Type} [∀ n, ContSet (S' n) (Vec ℝ n)]
variable [∀ n, Recentre (S' n) (Vec ℝ n)] [∀ n, CompactSet (S' n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every state of a run on `[0, T]` with inputs in `U ⊆ V`, less its free
motion and what `V`'s centre contributes, is one `recentre V`-input's
contribution. -/
theorem LinearSys.Trajectory.sub_mem_inputReach_recentre {sys : LinearSys 𝕋 n} {T : ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} (traj : sys.Trajectory (Set.Icc 0 T) R₀ U x u)
    {V : S' n} (hUV : construct U ⊆ construct V) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    x t - (exp (t • toRealMat sys.A) *ᵥ x 0
        + MatExp.expIntegral (toRealMat sys.A) t *ᵥ Recentre.centre V)
      ∈ sys.inputReach (Recentre.recentre V) t := by -- --- PROOF ---
  set A := toRealMat sys.A with hA
  set uc := Recentre.centre V with huc
  have hTt : Set.Icc (0:ℝ) t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc_right ht.2
  have hU : Bornology.IsBounded (construct U) := (CompactSet.isBounded_construct V).subset hUV
  have hvoc := traj.variation_of_constants hTt le_rfl ht.1 hU
  rw [sub_zero] at hvoc
  -- the input, less the centre, is an admissible input of `Ũ`
  have hmem₀ : ∀ s ∈ Set.Icc (0:ℝ) t, u s - uc ∈ construct (Recentre.recentre V) :=
    fun s hs => Recentre.sub_centre_mem_recentre (hUV (traj.input s (hTt hs)))
  have hmeas₀ : AEStronglyMeasurable (fun s => u s - uc) (volume.restrict (Set.Icc 0 t)) :=
    (traj.aestronglyMeasurable_input hTt).sub aestronglyMeasurable_const
  have hint₁ := intervalIntegrable_expSub_mulVec (A := A) (c := t) (S := 𝒮)
    (U := ({uc} : Set (Vec ℝ n))) ht.1 Bornology.isBounded_singleton
    (fun _ _ => Set.mem_singleton uc)
    aestronglyMeasurable_const
  have hint₀ := intervalIntegrable_expSub_mulVec (A := A) (c := t) ht.1
    (CompactSet.isBounded_construct (Recentre.recentre V)) hmem₀ hmeas₀
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
