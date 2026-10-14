module

public import CORALean.ContDynamics.LinParamSys.Operations.ParticularSolutionFloat
public import CORALean.ContDynamics.LinParamSys.Theorems.InputReachSubsetInputSolutionFloat
public import CORALean.ContDynamics.LinParamSys.Theorems.ReachStepkFloatOuter
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
public import CORALean.ContDynamics.LinearSys.Theorems.PropagateInputReach
public import CORALean.ContDynamics.LinearSys.Theorems.PropagateInputSolutionMono

@[expose] public section

/-!
# `particularSolutionFloat` holds what the input contributes at one member

`LinParamSys.inputReach_subset_particularSolution` in floats: at a member `A` of
`sys.A`, with `0 ∈ U` the input's contribution grows with time [1, Prop. 3.3],
is the one-step set propagated `k + 1` times [1, Prop. 3.2], and that one step
lies in `inputSolutionFloat`. Each propagator `e^{A t_j}` is in the window
`reachStepkFloat` computes.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic Matrix ContSet NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The recursion encloses the member's propagation of the one-step set, window
by window. -/
theorem LinParamSys.aux_propagate_subset_particularSolutionFloat
    (sys : LinParamSys ℐ[𝕋] n) {Δt : 𝕋} {η ρ : ℕ}
    (h2 : 2 ≤ η) (U : Zonotope (Vec 𝕋 n)) {A : Mat ℝ n n} (hA : A ∈ sys.A.construct) :
    ∀ (k : ℕ) {P : Zonotope (Vec 𝕋 n)}, sys.particularSolutionFloat Δt η ρ U k = some P →
    (LinearSys.mk A : LinearSys ℝ n).propagateInputSolution (toReal Δt)
        (sys.inputSolutionFloat Δt η U).construct (k + 1) ⊆ P.construct
  | 0, P, h => by
    -- `{0} + e^{A·0} P^R(Δt)` is `P^R(Δt)` itself
    simp only [LinParamSys.particularSolutionFloat, Option.some.injEq] at h
    subst h
    intro y hy
    simpa [LinearSys.propagateInputSolution] using hy
  | k + 1, P, h => by
    simp only [LinParamSys.particularSolutionFloat, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨PRtk, hPRtk, E, hE, rfl⟩ := h
    rw [LinearSys.propagateInputSolution]
    rintro _ ⟨a, ha, _, ⟨y, hy, rfl⟩, rfl⟩
    have hE' := sys.reachStepkFloat_outer h2 hE hA hy
    simp only [Scalar.toRealMat_real, Nat.cast_add, Nat.cast_one] at hE' ⊢
    exact Reduce.reduce_outer _ ρ (Plus.plus_outer PRtk E (Set.add_mem_add
      (sys.aux_propagate_subset_particularSolutionFloat h2 U hA k hPRtk ha) hE'))


-- =======================================  MAIN THEOREM  ======================================= --

/-- Everything an input in `U` holding the origin contributes under a member `A` by
any `t ≤ t_{k+1}` lies in `P^R(t_{k+1})` as `particularSolutionFloat` computes it. -/
theorem LinParamSys.inputReach_subset_particularSolutionFloat
    (sys : LinParamSys ℐ[𝕋] n) {Δt : 𝕋} {η ρ : ℕ}
    (hΔt : 0 < toReal Δt) (hη : sys.OrderAdmissibleFloat Δt Δt η)
    {A : Mat ℝ n n} (hA : A ∈ sys.A.construct) {U : Zonotope (Vec 𝕋 n)}
    (h0 : (0 : Vec ℝ n) ∈ U.construct) {k : ℕ} {P : Zonotope (Vec 𝕋 n)}
    (hP : sys.particularSolutionFloat Δt η ρ U k = some P) {t : ℝ} (ht0 : 0 ≤ t)
    (htk : t ≤ ((k + 1 : ℕ) : ℝ) * toReal Δt) :
    (LinearSys.mk A : LinearSys ℝ n).inputReach (S := 𝒵[𝕋]) U t
      ⊆ P.construct := by -- --- PROOF ---
  set L : LinearSys ℝ n := LinearSys.mk A
  have hbdd := CompactSet.isBounded_construct U
  -- [1, Thm. 3.1]: one step of the input under `A`, inside `inputSolutionFloat`
  have hΔ : L.inputReach (S := 𝒵[𝕋]) U (toReal Δt)
      ⊆ (sys.inputSolutionFloat Δt η U).construct :=
    sys.inputReach_subset_inputSolutionFloat hΔt hη hA U
  calc L.inputReach (S := 𝒵[𝕋]) U t
      -- [1, Prop. 3.3]: `0 ∈ U`, so the window's right end bounds every earlier time
      ⊆ L.inputReach (S := 𝒵[𝕋]) U (((k + 1 : ℕ) : ℝ) * toReal Δt) :=
        L.inputReach_mono hbdd h0 ht0 htk
    -- [1, Prop. 3.2]: exactly the one-step set, propagated `k + 1` times
    _ = L.propagateInputSolution (toReal Δt)
      (L.inputReach (S := 𝒵[𝕋]) U (toReal Δt)) (k + 1) :=
      (L.propagateInputSolution_inputReach hΔt.le hbdd ⟨0, h0⟩ (k + 1)).symm
    _ ⊆ L.propagateInputSolution (toReal Δt) (sys.inputSolutionFloat Δt η U).construct (k + 1) :=
      L.propagateInputSolution_mono (toReal Δt) hΔ (k + 1)
    _ ⊆ P.construct := sys.aux_propagate_subset_particularSolutionFloat hη.1 U hA k hP

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
