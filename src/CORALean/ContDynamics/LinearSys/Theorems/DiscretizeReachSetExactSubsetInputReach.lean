module

public import CORALean.ContDynamics.LinearSys.Operations.Discretize
public import CORALean.ContDynamics.LinearSys.Operations.StepInputConst
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralMemInputReach
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSeparation
public import CORALean.ContDynamics.LinearSysDT.Definitions.ReachSetExact

@[expose] public section

/-!
# The discrete reachable set, under constant-input steps, sits inside `inputReach`

A point of `inputReach` is exhibited here by a genuine piecewise-constant input, and with
`reachSetExact_eq` the inclusion continues into `reachSetExact` itself: a trajectory being
Carathéodory, that input drives a run. Driven by induction on the step count:
`inputReach_separation` supplies the one step `e^{Δt A} P^R(kΔt) + P^R(Δt) ⊆ P^R((k+1)Δt)`, and
`expIntegral_mem_inputReach` places `stepInputConst c Δt` inside `P^R(Δt)`. `hne` and `hbdd` are not
part of the CORA algorithm modelled; they are what the `k = 0` base case and `inputReach_separation`
need from `U`. Nonemptiness is all the base case needs: holding any one point of `U` over `[0, 0]`
is admissible and contributes the empty integral, `0`.

## Inputs
* `sys` – linear system
* `Δt` – sampling step
* `R₀` – initial set
* `U` – input set
* `Ud` – sampled input set
* `k` – number of steps

## Hypotheses
* `hΔt` – step length positive
* `hbdd` – input set bounded
* `hne` – input set nonempty
* `hUd` – sampled inputs are constant steps of input values

## Conclusion
* the discrete reachable set lies in the propagated start plus the input reach
-/

-- Authors:       Claude Opus 5
-- Written:       15-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `e^{cA}e^{dA} = e^{(c+d)A}`: the two exponentials commute, both being
powers of the same matrix. -/
theorem aux_exp_add (A : Mat ℝ n n) (c d : ℝ) : exp (c • A) * exp (d • A) = exp ((c + d) • A) := by
  have hc : Commute (c • A) (d • A) := ((Commute.refl A).smul_left c).smul_right d
  rw [add_smul]
  exact (exp_add_of_commute hc).symm

/-- Over `[0, 0]` any admissible input contributes the empty integral, and a
nonempty `U` has one: hold it at any of its points. -/
theorem aux_zero_mem_inputReach_zero (sys : LinearSys 𝕋 n) (U : S n)
    (hne : (construct U).Nonempty) : (0 : Vec ℝ n) ∈ sys.inputReach U 0 :=
  ⟨fun _ => hne.some, fun _ _ => hne.some_mem, aestronglyMeasurable_const, by simp⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every point the exact discrete recursion reaches in `k` steps is `e^{kΔt A}`
applied to a point of `R₀` plus a point of `U`'s own `kΔt`-window input reach
— the zero-order-hold input that realises it is exhibited, not asserted. -/
theorem LinearSys.discretize_reachSetExact_subset_inputReach (sys : LinearSys 𝕋 n) {Δt : ℝ}
    (hΔt : 0 < Δt) (R₀ U Ud : S n) (hbdd : Bornology.IsBounded (construct U))
    (hne : (construct U).Nonempty)
    (hUd : construct Ud ⊆ (fun c => sys.stepInputConst c Δt) '' construct U)
    (k : ℕ) : -- --- CONCL ---
    (sys.discretize Δt).reachSetExact R₀ Ud k
      ⊆ (exp (((k : ℝ) * Δt) • toRealMat sys.A)).mulVecLin '' construct R₀
        + sys.inputReach U ((k : ℝ) * Δt) := by -- --- PROOF ---
  induction k with
  | zero =>
    intro y hy
    have hy' : y ∈ construct R₀ := by simpa [LinearSysDT.reachSetExact] using hy
    simp only [Nat.cast_zero, zero_mul]
    refine ⟨y, ⟨y, hy', ?_⟩, 0, aux_zero_mem_inputReach_zero sys U hne, ?_⟩ <;> simp
  | succ k ih =>
    intro y hy
    -- the matrix part and the fresh input `d`, itself a step contribution of some `c ∈ U`
    obtain ⟨_, ⟨y', hy', rfl⟩, d, hd, rfl⟩ := hy
    obtain ⟨c, hc, rfl⟩ := hUd hd
    obtain ⟨_, ⟨r, hr, rfl⟩, p, hp, rfl⟩ := ih hy'
    -- `discretize`'s matrix is `e^{ΔtA}`, and `mulVecLin` is `*ᵥ` under a different name
    simp only [Matrix.mulVecLin_apply, LinearSys.discretize, Scalar.toRealMat_real]
    have hsep := sys.inputReach_separation (a := (k : ℝ) * Δt) (b := Δt)
      (mul_nonneg (Nat.cast_nonneg k) hΔt.le) hΔt.le hbdd
    have hmemsum : exp (Δt • toRealMat sys.A) *ᵥ p + sys.stepInputConst c Δt
        ∈ sys.inputReach U ((k : ℝ) * Δt + Δt) :=
      hsep (Set.add_mem_add (Set.mem_image_of_mem _ hp)
        (sys.expIntegral_mem_inputReach hΔt.le hc))
    have hcast : (((k : ℕ) + 1 : ℕ) : ℝ) * Δt = (k : ℝ) * Δt + Δt := by push_cast; ring
    have hval : exp (Δt • toRealMat sys.A) *ᵥ (exp (((k : ℝ) * Δt) • toRealMat sys.A) *ᵥ r + p)
        + sys.stepInputConst c Δt
        = exp (((k : ℝ) * Δt + Δt) • toRealMat sys.A) *ᵥ r
          + (exp (Δt • toRealMat sys.A) *ᵥ p + sys.stepInputConst c Δt) := by
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, aux_exp_add, add_comm Δt ((k : ℝ) * Δt)]
      abel
    rw [hcast, hval]
    exact ⟨exp (((k : ℝ) * Δt + Δt) • toRealMat sys.A) *ᵥ r, ⟨r, hr, rfl⟩,
      exp (Δt • toRealMat sys.A) *ᵥ p + sys.stepInputConst c Δt, hmemsum, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
