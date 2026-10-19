module

public import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableInput
public import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableInputReflected
public import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionOuter
public import CORALean.ContDynamics.LinearSys.Theorems.IntervalIntegrableExpSubMulVec
public import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants
public import CORALean.ContDynamics.NonlinearSys.Theorems.LinInputOuter
public import CORALean.ContDynamics.NonlinearSys.Theorems.LinearizeWindow

@[expose] public section

/-!
# A linearized step, solution by solution: the representation behind the inner set

[1, Prop. 1]'s proof writes every solution at the end of a step as
`x(Δt) = e^{AΔt} x(0) + R_con + z(x(0))`, `z(x(0)) ∈ R̂_err` (21). Here it is derived from the
linearization: a run under the constant input `u₀` that stays in the region `R` of an
`AbstractionError` certificate `L` solves `ẋ = Ax + w + l(t)`, `w = f(x✱,u✱) - Ax✱ + B(u₀ - u✱)`,
`l(t) ∈ L` (`IsTrajectory.linearize`); the variation of constants splits off
`R_con = ∫₀^Δt e^{A(Δt-s)} w ds`, and what `l` contributes lies in `inputSolution Δt η L`
(`inputSolution_outer`), CORA's `particularSolution_timeVarying(linsys, VerrorDyn, Δt)`, which
is `R̂_err`. The confinement of the run to `R` is the hypothesis `hR`, as everywhere in
conservative linearization.

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
  Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
  8:2033-2038, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace MeasureTheory Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- (21) of [1, Prop. 1]'s proof: `x(Δt) - (e^{AΔt} x(0) + R_con)` lies in what the abstraction
error contributes over the step. -/
theorem NonlinearSys.IsTrajectory.sub_mem_inputSolution [Mtimes ℐ S] {sys : NonlinearSys n m}
    {R₀ L : S n} {U : S m} {x : ℝ → Vec ℝ n} {u₀ : Vec ℝ m} {A : Mat ℝ n n}
    {B : Mat ℝ n m} {xs : Vec ℝ n} {us : Vec ℝ m} {R : Set (Vec ℝ n)} {Δt : ℝ}
    {y : ℝ → Vec ℝ sys.q} (traj : sys.IsTrajectory (Set.Icc 0 Δt) R₀ U x (fun _ => u₀) y)
    (cert : AbstractionError sys.f A B xs us R (construct U) L)
    (hR : ∀ t ∈ Set.Icc 0 Δt, x t ∈ R) (hΔt : 0 < Δt) (η : ℕ)
    (hε : ‖Δt • A‖ / ((η : ℝ) + 2) < 1)
    (hconv : Convex ℝ (construct L)) (hclosed : IsClosed (construct L))
    (hbdd : Bornology.IsBounded (construct L))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ) (MatExp.inputRemainder A Δt η) L)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder A Δt η) L)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder A Δt η) L))) : -- --- CONCL ---
    x Δt - (exp (Δt • A) *ᵥ x 0 + ∫ s in (0:ℝ)..Δt, exp ((Δt - s) • A) *ᵥ
      (sys.f xs us - A *ᵥ xs + B *ᵥ (u₀ - us))) ∈
        construct ((NonlinearSys.linearize A).inputSolution Δt η L) := by -- --- PROOF ---
  set w : Vec ℝ n := sys.f xs us - A *ᵥ xs + B *ᵥ (u₀ - us)
  have hu₀ : u₀ ∈ construct U := traj.input 0 ⟨le_rfl, hΔt.le⟩
  set l : ℝ → Vec ℝ n := fun t => sys.f (x t) u₀ - A *ᵥ x t - w
  have hl : ∀ t ∈ Set.Icc 0 Δt, l t ∈ construct L := fun t ht => by
    have h := cert.encloses (x t) (hR t ht) u₀ hu₀
    have e : l t = sys.f (x t) u₀ - (sys.f xs us + A *ᵥ (x t - xs) + B *ᵥ (u₀ - us)) := by
      simp only [l, w, Matrix.mulVec_sub]
      abel
    rw [e]
    exact h
  -- the run as a linear one, with input `ũ(t) = f(x(t), u₀) - A x(t) = w + l(t)` in `{w} + L`
  have hVb : Bornology.IsBounded (({w} : Set (Vec ℝ n)) + construct L) :=
    Bornology.isBounded_singleton.add hbdd
  have lin := traj.linearize_window (t₀ := 0) (A := A) (V := {w} + construct L) hΔt.le
    (by rw [zero_add]) fun t ht => by
      rw [zero_add] at ht
      exact Set.mem_add.mpr ⟨w, rfl, l t, hl t ht, by simp only [l]; abel⟩
  simp only [zero_add] at lin
  have hlm : AEStronglyMeasurable l (volume.restrict (Set.Icc 0 Δt)) :=
    (lin.aestronglyMeasurable_input subset_rfl).sub aestronglyMeasurable_const
  -- the variation of constants, and its integral split into `w`'s part and `l`'s
  have hw : IntervalIntegrable (fun s => exp ((Δt - s) • A) *ᵥ w) volume 0 Δt :=
    (Continuous.matrix_mulVec (by fun_prop) continuous_const).intervalIntegrable 0 Δt
  have hlI : IntervalIntegrable (fun s => exp ((Δt - s) • A) *ᵥ l s) volume 0 Δt :=
    intervalIntegrable_expSub_mulVec hΔt.le hbdd hl hlm
  -- `x(Δt) = e^{AΔt} x(0) + ∫ e^{A(Δt-s)} ũ(s) ds`
  have hvoc : x Δt = exp ((Δt - 0) • A) *ᵥ x 0 + ∫ s in (0:ℝ)..Δt, exp ((Δt - s) • A) *ᵥ
      (sys.f (x s) u₀ - A *ᵥ x s) := lin.variation_of_constants subset_rfl le_rfl hΔt.le hVb
  have hsplit : (∫ s in (0:ℝ)..Δt, exp ((Δt - s) • A) *ᵥ (sys.f (x s) u₀ - A *ᵥ x s))
      = (∫ s in (0:ℝ)..Δt, exp ((Δt - s) • A) *ᵥ w)
        + ∫ s in (0:ℝ)..Δt, exp ((Δt - s) • A) *ᵥ l s := by
    rw [← intervalIntegral.integral_add hw hlI]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [l, ← Matrix.mulVec_add]
    congr 1
    abel
  -- what `l` contributes is in `inputSolution`
  have hmem : (∫ s in (0:ℝ)..Δt, exp ((Δt - s) • A) *ᵥ l s) ∈
      construct ((NonlinearSys.linearize A).inputSolution Δt η L) :=
    LinearSys.inputSolution_outer (NonlinearSys.linearize A) hΔt η hε hconv hclosed
      hbdd hRconv hRclosed hRbdd (u := l)
      (fun τ hτ => hl (Δt - τ) ⟨by linarith [hτ.2], by linarith [hτ.1]⟩)
      ((lin.aestronglyMeasurable_input_reflected (c := Δt) (r := Δt)
        (by rw [sub_self])).sub aestronglyMeasurable_const)
  rw [hvoc, hsplit, sub_zero]
  convert hmem using 1
  abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
