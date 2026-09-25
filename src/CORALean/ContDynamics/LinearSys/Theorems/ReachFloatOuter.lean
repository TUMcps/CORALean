import CORALean.ContDynamics.LinearSys.Operations.ReachFloat
import CORALean.ContDynamics.LinearSys.Theorems.ReachOrderFloatSpec
import CORALean.ContDynamics.LinearSys.Theorems.ReachStepkFloatOuter
import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalStepFloatOuter

/-!
# `reachFloat` holds the exact flow over every window

At `t = t_k + s`, `s ∈ [0, Δt]`, the flow is `e^{A t_k} e^{As} x₀`:
`timeIntervalStepFloat_outer` puts `e^{As} x₀` in the first window,
`Reduce.reduce_outer` keeps it there, and `reachStepkFloat_outer` carries it to
window `k`. Nothing is asked of `η`: the order the run used is the one
`reachOrderFloat_spec` certifies. `Δt` must be positive, the one hypothesis the
correction matrix `F` needs; the windows themselves ask nothing of its sign.
-/

-- Authors:       Tobias Ladner
-- Written:       25-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic NormedSpace Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A `mapM` into `Option` that succeeds has one result per entry, each the
function's value there. -/
theorem LinearSys.aux_mapM_some {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' →
      ∃ hlen : l'.length = l.length, ∀ (i : ℕ) (hi : i < l'.length),
        f (l[i]'(hlen ▸ hi)) = some l'[i] := by -- --- PROOF ---
  intro l
  induction l with
  | nil =>
    intro l' h
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | cons a l ih =>
    intro l' h
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    obtain ⟨hlen, hget⟩ := ih hbs
    -- the head is `f a`, the tail the induction's
    refine ⟨by simp [hlen], fun i hi => ?_⟩
    cases i with
    | zero => exact hb
    | succ i => exact hget i (Nat.lt_of_succ_lt_succ hi)


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.reachFloat_outer (sys : LinearSys 𝕋 n) {X₀ : Zonotope 𝕋 n} {Δt : 𝕋}
    {η ρ N : ℕ} {Rs : List (Zonotope 𝕋 n)} (hΔt : 0 < toReal Δt)
    (h : sys.reachFloat X₀ Δt η ρ N = some Rs) :
    Rs.length = N ∧ ∀ (k : ℕ) (hk : k < Rs.length), ∀ x₀ ∈ X₀.construct,
      ∀ s ∈ Set.Icc 0 (toReal Δt),
        exp (((k : ℝ) * toReal Δt + s) • Scalar.toRealMat sys.A) *ᵥ x₀
          ∈ Rs[k].construct := by -- --- PROOF ---
  simp only [LinearSys.reachFloat, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨η', hη', hRs⟩ := h
  have hadm := (LinearSys.reachOrderFloat_spec hη').1
  obtain ⟨hlen, hget⟩ := LinearSys.aux_mapM_some hRs
  rw [List.length_range] at hlen
  refine ⟨hlen, fun k hk x₀ hx₀ s ⟨hs0, hs⟩ => ?_⟩
  -- `e^{As} x₀` is in the first window, reduced or not
  have hτ₀ := Reduce.reduce_outer (sys.timeIntervalStepFloat Δt η' X₀) ρ
    (sys.timeIntervalStepFloat_outer hΔt hadm X₀ hx₀ hs0 hs)
  have hwin := hget k hk
  simp only [List.getElem_range] at hwin
  -- `e^{A (t_k + s)} = e^{A t_k} e^{As}`, both powers of the same matrix
  have hc : Commute (((k : ℝ) * toReal Δt) • Scalar.toRealMat sys.A)
      (s • Scalar.toRealMat sys.A) := ((Commute.refl _).smul_left _).smul_right _
  have hexp : exp (((k : ℝ) * toReal Δt + s) • Scalar.toRealMat sys.A) *ᵥ x₀
      = exp (((k : ℝ) * toReal Δt) • Scalar.toRealMat sys.A)
        *ᵥ (exp (s • Scalar.toRealMat sys.A) *ᵥ x₀) := by
    have h := exp_add_of_commute hc
    rw [← add_smul] at h
    rw [Matrix.mulVec_mulVec]
    exact congrArg (· *ᵥ x₀) h
  rw [hexp]
  exact sys.reachStepkFloat_outer hwin hτ₀

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
