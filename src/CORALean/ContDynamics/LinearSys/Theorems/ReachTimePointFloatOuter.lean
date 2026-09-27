import CORALean.ContDynamics.LinearSys.Operations.ReachTimePointFloat
import CORALean.ContDynamics.LinearSys.Theorems.ReachOrderFloatSpec
import CORALean.ContDynamics.LinearSys.Theorems.ReachStepkFloatOuter

/-!
# `reachTimePointFloat` holds the exact flow at every sample time

At `t_k = k Δt`, the flow is `e^{A t_k} x₀`: `reachStepkFloat_outer` carries
every point of `X₀` through the window's matrix directly, `k = 0` included --
`e^{A · 0} = I` needs nothing beyond that same lemma. `η'` is the order the
run used, certified admissible by `reachOrderFloat_spec` exactly as
`reachFloat_outer` uses it; `aux_mapM_some` reads one `mapM` result per `k`.
-/

-- Authors:       Tobias Ladner
-- Written:       27-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic NormedSpace Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A `mapM` into `Option` that succeeds has one result per entry, each the
function's value there -- `ReachFloatOuter.lean`'s own lemma, copied rather
than imported, since an `aux_` name stays local to the file that declares it. -/
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
    refine ⟨by simp [hlen], fun i hi => ?_⟩
    cases i with
    | zero => exact hb
    | succ i => exact hget i (Nat.lt_of_succ_lt_succ hi)


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.reachTimePointFloat_outer (sys : LinearSys 𝕋 n) {X₀ : Zonotope 𝕋 n} {Δt : 𝕋}
    {η N : ℕ} {Rs : List (Zonotope 𝕋 n)} (h : sys.reachTimePointFloat X₀ Δt η N = some Rs) :
    Rs.length = N + 1 ∧ ∀ (k : ℕ) (hk : k < Rs.length), ∀ x₀ ∈ X₀.construct,
      exp (((k : ℝ) * toReal Δt) • Scalar.toRealMat sys.A) *ᵥ x₀
        ∈ Rs[k].construct := by -- --- PROOF ---
  simp only [LinearSys.reachTimePointFloat, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨η', hη', hRs⟩ := h
  have hadm := (LinearSys.reachOrderFloat_spec hη').1
  obtain ⟨hlen, hget⟩ := LinearSys.aux_mapM_some hRs
  rw [List.length_range] at hlen
  refine ⟨hlen, fun k hk x₀ hx₀ => ?_⟩
  have hwin := hget k hk
  simp only [List.getElem_range] at hwin
  -- window `k` is `reachStepkFloat` at `X₀` directly, `k = 0` included
  exact sys.reachStepkFloat_outer hadm.1 hwin hx₀

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
