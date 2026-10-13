import CORALean.ContDynamics.Reach.Theorems.StepsSpecToReal
import CORALean.ContDynamics.LinearSys.Operations.ReachFloatInput
import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralConstInput
import CORALean.ContDynamics.LinearSys.Theorems.ExpMemExpIntervalFloat
import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolutionFloat
import CORALean.ContDynamics.LinearSys.Theorems.ReachFloatInputStepInvariant
import CORALean.ContDynamics.LinearSys.Theorems.ReachOrderFloatSpec
import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalStepFloatOuter

/-!
# Every state of `reachFloatInput`'s loop holds what it owes

By induction on the pass, `reachFloatInputStep_invariant` the step. The start:
`H(t_1) = [e^{AΔt}] X₀ ⊕ P̃(Δt)`; `H(τ_0)` is the homogeneous time-interval step
`timeIntervalStepFloat_outer` covers plus `P̃^R(τ_0)`, which holds
`∫₀^τ e^{Aσ}dσ ũ` as the constant input `ũ` over `[0, τ]` with values in
`[0, ũ] ∋ 0` (`inputReach_mono`); and `P^R(t_1)` and the propagated one-step
set are both `P^R(Δt)`, by `inputReach_subset_inputSolutionFloat`.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic NormedSpace Matrix MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A successful run's loop states, the step positive and `N` of them spanning
the horizon, each holding what `ReachFloatInputInvariant` asks at its pass. -/
theorem LinearSys.reachFloatInput_invariant (sys : LinearSys 𝕋 n) (B : Mat 𝕋 n m)
    {params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 m)) ℚ}
    {options : LinearSys.ReachOptions 𝕋} {Rti Rtp : List (Zonotope (Vec 𝕋 n))}
    (h : sys.reachFloatInput B params options = some (Rti, Rtp)) :
    0 < toReal options.timeStep ∧ ∃ N : ℕ,
      (N : ℝ) * toReal options.timeStep = (params.tFinal : ℝ) - params.tStart ∧
      ∃ S : List (Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n) ×
        Zonotope (Vec 𝕋 n)),
        S.length = N ∧ Rti = S.map (fun s => s.2.1 ⊞ s.2.2.1) ∧
        Rtp = params.R0 :: S.map (fun s => s.1 ⊞ s.2.2.1) ∧
        ∀ (k : ℕ) (hk : k < S.length), sys.ReachFloatInputInvariant (toReal options.timeStep)
          params.R0.construct (Recentre.centre
            (Mtimes.mtimes (𝕄 := Mat 𝕋) (S := fun k => Zonotope (Vec 𝕋 k)) B params.U))
          (Recentre.recentre (Mtimes.mtimes (𝕄 := Mat 𝕋) (S := fun k => Zonotope (Vec 𝕋 k)) B
            params.U)) k S[k] := by -- --- PROOF ---
  obtain ⟨X₀, U, tStart, tFinal⟩ := params
  obtain ⟨Δt, η, ρ⟩ := options
  dsimp only at h ⊢
  simp only [LinearSys.reachFloatInput, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨N, hN, η', hη', rfl, rfl⟩ := h
  obtain ⟨hΔt, hNΔt⟩ := Reach.steps_spec_toReal hN
  have hadm := (LinearSys.reachOrderFloat_spec hη').1
  refine ⟨hΔt, N, hNΔt, _, List.length_iterate _ _ _, rfl, rfl, fun k hk => ?_⟩
  rw [List.getElem_iterate]
  clear hk
  -- the input set in the state space, its centre, and one step's `[e^{AΔt}]`
  set V := Mtimes.mtimes (𝕄 := Mat 𝕋) (S := fun k => Zonotope (Vec 𝕋 k)) B U with hV
  set A := Scalar.toRealMat sys.A with hA
  set ũ := Recentre.centre V with hũ
  have heA := sys.exp_mem_expIntervalFloat hadm (t := toReal Δt) le_rfl le_rfl
  have hmt : ∀ {Z : Zonotope (Vec 𝕋 n)} {z : Vec ℝ n}, z ∈ Z.construct → exp (toReal Δt • A) *ᵥ z
      ∈ ContSet.construct (Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))
        (S := fun k => Zonotope (Vec 𝕋 k))
        (sys.expIntervalFloat Δt Δt η') Z) :=
    fun {Z} {_} hz => Mtimes.mtimes_outer (𝕄 := fun m n => Interval (Mat 𝕋 m n))
      (S := fun k => Zonotope (Vec 𝕋 k)) _ Z
      (Set.mem_biUnion heA (Set.mem_image_of_mem _ hz))
  -- `{ũ}` and `[0, ũ]` hold what they are built from
  have hpt : ũ ∈ (Interval.point V.c).zonotope.construct :=
    Interval.zonotope_contains _ (Interval.mem_point V.c)
  have hzero : (0 : Vec ℝ n) ∈ (Interval.point fun _ : Fin n => (zero : 𝕋)).zonotope.construct := by
    have h0 := Interval.zonotope_contains _ (Interval.mem_point fun _ : Fin n => (zero : 𝕋))
    rwa [show RealImage.realImage (fun _ : Fin n => (zero : 𝕋)) = (0 : Vec ℝ n) from
      funext fun _ => toReal_zero] at h0
  set seg := LinComb.linComb (Interval.point fun _ : Fin n => (zero : 𝕋)).zonotope
    (Interval.point V.c).zonotope with hseg
  have h0seg : (0 : Vec ℝ n) ∈ seg.construct := by
    refine LinComb.linComb_outer (Interval.point fun _ : Fin n => (zero : 𝕋)).zonotope
      (Interval.point V.c).zonotope ?_
    exact ⟨0, hzero, ũ, hpt, 1, ⟨zero_le_one, le_rfl⟩, by simp⟩
  have hũseg : ũ ∈ seg.construct := by
    refine LinComb.linComb_outer (Interval.point fun _ : Fin n => (zero : 𝕋)).zonotope
      (Interval.point V.c).zonotope ?_
    exact ⟨0, hzero, ũ, hpt, 0, ⟨le_rfl, zero_le_one⟩, by simp⟩
  -- the constant `ũ` held over `[0, τ]` is an admissible input of any set holding `ũ`
  have hconst : ∀ {W : Zonotope (Vec 𝕋 n)}, ũ ∈ W.construct → ∀ {τ : ℝ}, 0 ≤ τ →
      Real.MatExp.expIntegral A τ *ᵥ ũ ∈ sys.inputReach (S := fun k => Zonotope (Vec 𝕋 k)) W τ :=
    fun hW _ hτ => ⟨fun _ => ũ, fun _ _ => hW, aestronglyMeasurable_const,
      (Real.MatExp.expIntegral_constInput A ũ hτ).symm⟩
  have hPu := sys.inputReach_subset_inputSolutionFloat hΔt hadm _ (hconst hpt hΔt.le)
  induction k with
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact sys.reachFloatInputStep_invariant hΔt.le ρ heA hPu ih
  | zero =>
    have h1 : (((0 + 1 : ℕ) : ℝ) * toReal Δt) = toReal Δt := by simp
    refine ⟨fun x₀ hx₀ => ?_, fun x₀ hx₀ τ hτ => ?_, ?_, ?_⟩
    · -- `H(t_1)`
      rw [h1]
      exact Reduce.reduce_outer _ ρ (Plus.plus_outer _ _ (Set.add_mem_add (hmt hx₀) hPu))
    · -- `H(τ_0)`: the homogeneous step, and the constant over `[0, τ]` inside `P̃^R(τ_0)`
      have hτ0 : ((0 : ℕ) : ℝ) * toReal Δt + τ = τ := by simp
      rw [hτ0]
      have hc := sys.inputReach_subset_inputSolutionFloat hΔt hadm seg
        (sys.inputReach_mono (CompactSet.isBounded_construct seg) h0seg hτ.1 hτ.2
          (hconst hũseg hτ.1))
      exact Plus.plus_outer (sys.timeIntervalStepFloat Δt η' X₀) (sys.inputSolutionFloat Δt η' seg)
        (Set.add_mem_add (sys.timeIntervalStepFloat_outer hΔt hadm X₀ hx₀ hτ.1 hτ.2) hc)
    · -- `P^R(t_1)`
      rw [h1]
      exact sys.inputReach_subset_inputSolutionFloat hΔt hadm _
    · -- the one-step set, carried across `t_0 = 0`
      rintro _ ⟨y, hy, rfl⟩
      simp only [Nat.cast_zero, zero_mul, zero_smul, exp_zero, Matrix.one_mulVec]
      exact sys.inputReach_subset_inputSolutionFloat hΔt hadm _ hy

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
