module

public import CORALean.ContDynamics.LinearSys.Operations.InputReach
public import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableInput
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralConstInput
public import CORALean.ContDynamics.LinearSys.Theorems.IntervalIntegrableExpSubMulVec
public import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants
public import CORALean.ContSet.ContSet.Definitions.Interfaces
public import CORALean.ContSet.ContSet.Theorems.Basic

@[expose] public section

/-!
# A run is its free motion, its constant input, and a recentered input's share

[1, Sec. III-A]'s split, at one run: with inputs in `U ⊆ V` and `V = ũ ⊕ Ũ` by
`Recenter`, `x(t) = e^{At} x(0) + ∫₀ᵗ e^{Aσ}dσ ũ + ∫₀ᵗ e^{A(t-s)} (u(s) - ũ) ds`,
and the last term is one admissible `Ũ`-input's contribution, `inputReach Ũ t`.
The argument `WithInputSplit.reach_outer` makes inline, named so that a float
reach can state its windows against the same three pieces.

## Inputs
* `sys` – linear system
* `T` – horizon
* `R₀` – initial set
* `U` – input set
* `x` – state trajectory
* `u` – input signal
* `V` – enclosing set
* `t` – time

## Hypotheses
* `traj` – signal is a canonical trajectory
* `hUV` – input set lies in the enclosing set
* `ht` – time within the horizon

## Conclusion
* the run minus free motion and center contribution lies in the recentered input reach

## References

* [1] [M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control,
      2014.](../../../../../references/2014/althoff-tac-nonlinear-dae.md)
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
variable [∀ n, Recenter (S' n) (Vec ℝ n)] [∀ n, CompactSet (S' n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every state of a run on `[0, T]` with inputs in `U ⊆ V`, less its free
motion and what `V`'s center contributes, is one `recenter V`-input's
contribution. -/
theorem LinearSys.IsCanonicalTrajectory.sub_mem_inputReach_recenter {sys : LinearSys 𝕋 n} {T : ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} (traj : sys.IsCanonicalTrajectory (Set.Icc 0 T) R₀ U x u)
    {V : S' n} (hUV : construct U ⊆ construct V) {t : ℝ} (ht : t ∈ Set.Icc 0 T) : -- --- CONCL ---
    x t - (exp (t • toRealMat sys.A) *ᵥ x 0
        + MatExp.expIntegral (toRealMat sys.A) t *ᵥ Recenter.center V)
      ∈ sys.inputReach (Recenter.recenter V) t := by -- --- PROOF ---
  set A := toRealMat sys.A with hA
  set uc := Recenter.center V with huc
  have hTt : Set.Icc (0:ℝ) t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc_right ht.2
  have hU : Bornology.IsBounded (construct U) := (CompactSet.isBounded_construct V).subset hUV
  have hvoc := traj.variation_of_constants hTt le_rfl ht.1 hU
  rw [sub_zero] at hvoc
  -- the input, less the center, is an admissible input of `Ũ`
  have hmem₀ : ∀ s ∈ Set.Icc (0:ℝ) t, u s - uc ∈ construct (Recenter.recenter V) :=
    fun s hs => Recenter.sub_center_mem_recenter (hUV (traj.input s (hTt hs)))
  have hmeas₀ : AEStronglyMeasurable (fun s => u s - uc) (volume.restrict (Set.Icc 0 t)) :=
    (traj.aestronglyMeasurable_input hTt).sub aestronglyMeasurable_const
  have hint₁ := intervalIntegrable_expSub_mulVec (A := A) (c := t) (S := 𝒮)
    (U := ({uc} : Set (Vec ℝ n))) ht.1 Bornology.isBounded_singleton
    (fun _ _ => Set.mem_singleton uc)
    aestronglyMeasurable_const
  have hint₀ := intervalIntegrable_expSub_mulVec (A := A) (c := t) ht.1
    (CompactSet.isBounded_construct (Recenter.recenter V)) hmem₀ hmeas₀
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
