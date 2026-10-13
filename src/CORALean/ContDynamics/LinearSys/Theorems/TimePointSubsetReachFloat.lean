module

public import CORALean.ContDynamics.Reach.Theorems.StepsSpecToReal
public import CORALean.ContDynamics.LinearSys.Operations.ReachFloat
public import CORALean.ContDynamics.LinearSys.Operations.TimePoint
public import CORALean.ContDynamics.LinearSys.Theorems.ReachOrderFloatSpec
public import CORALean.ContDynamics.LinearSys.Theorems.TimePointStepFloatOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact

@[expose] public section

/-!
# The nominal time-point set refines `reachFloat`'s, at a `Real.Zonotope`

`sys.reachFloat`'s time-point sets `Rtp`, computed in `𝕋`, enclose the same
recursion the nominal `timePoint` runs at a `Real.Zonotope`, given the initial
sets agree that way: `Real.Zonotope.mtimes_exact` makes `timePoint`'s own step
exact, so a point of `timePoint (k + 1)`'s set is `e^{AΔt} x` for some `x` of
`timePoint k`'s, and `ih` puts that `x` in `Rtp[k]`; `timePointStepFloat_outer`
and `Reduce.reduce_outer` carry it into `Rtp[k + 1]`, `reachFloat`'s own step
from there. Time points only: a window's nominal `timeIntervalStep` widens by
a correction matrix at the *nominal* `sys.A`, while `reachFloat`'s window widens
by one at the *interval* enclosure of it, and the two error terms are not
compared here.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic NormedSpace Matrix ContSet

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every `k` in range: the nominal time-point set at `k · toReal Δt` is inside
`reachFloat`'s float one. -/
theorem LinearSys.timePoint_subset_reachFloat (sys : LinearSys 𝕋 n)
    {X₀ : Real.Zonotope (Vec ℝ n)} {X₀float : Zonotope (Vec 𝕋 n)}
    (hX₀ : construct X₀ ⊆ X₀float.construct) {tStart tFinal : ℚ}
    {options : LinearSys.ReachOptions 𝕋} {Rti Rtp : List (Zonotope (Vec 𝕋 n))}
    (h : sys.reachFloat ⟨X₀float, tStart, tFinal⟩ options = some (Rti, Rtp)) :
    ∀ (k : ℕ) (hk : k < Rtp.length),
      construct (sys.timePoint (S := fun n => Real.Zonotope (Vec ℝ n)) (toReal options.Δt)
        X₀ k) ⊆ Rtp[k].construct := by -- --- PROOF ---
  obtain ⟨Δt, η, ρ⟩ := options
  dsimp only at h ⊢
  simp only [LinearSys.reachFloat, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨N, -, η', hη', -, rfl⟩ := h
  have hadm := (LinearSys.reachOrderFloat_spec hη').1
  intro k hk
  rw [List.getElem_iterate]
  clear hk
  induction k with
  | zero => exact hX₀
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    -- `timePoint`'s own step is exact, at a `Real.Zonotope`
    have hstep : construct (sys.timePoint (S := fun n => Real.Zonotope (Vec ℝ n))
          (toReal Δt) X₀ (k + 1))
        = (exp (toReal Δt • Scalar.toRealMat sys.A) *ᵥ ·) ''
          construct (sys.timePoint (S := fun n => Real.Zonotope (Vec ℝ n)) (toReal Δt) X₀ k) :=
      (Real.Zonotope.mtimes_exact _ _).symm
    rw [hstep]
    rintro _ ⟨x, hx, rfl⟩
    exact Reduce.reduce_outer (sys.timePointStepFloat Δt η' _) ρ
      (sys.timePointStepFloat_outer hadm _ (ih hx))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
