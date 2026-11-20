module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalConstCorrectionMatrixTightFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalCorrectionMatrixTightFloat
public import CORALean.ContDynamics.LinearSys.Operations.TaylorMatricesFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ExpRemainderMatLeExpRemainderSquaringFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpRemainderMat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalTaylorFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ExpMemExpSquaringFloat
public import CORALean.ContSet.Interval.Float.Theorems.SmulOuter
public import CORALean.ContDynamics.LinearSys.Theorems.HalvingsFloatSpec
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint

@[expose] public section

/-!
# `taylorMatricesFloat` encloses CORA's correction terms

The bound `W` of `taylorMatricesFloat` is over `E(Δt,η)`: `e^{|A|Δt}` is in the squarings at the
halvings found, admissible at order `16` by `halvingsFloat_spec`, and the series in its Taylor box.
So `[F]` holds the curvature term `e^{tA} − I − (t/Δt)(e^{ΔtA} − I)` and `[G]` the input term
`∫₀ᵗ e^{τA} − (t/Δt) ∫₀^Δt e^{τA}` for every `t ∈ [0, Δt]`, at an order of at least `2`.

## Inputs
* `sys` – float linear system
* `Δt` – float step length
* `m` – the order less `2`
* `t` – time in the step

## Hypotheses
* `hΔt` – positive step length
* `ht0` – `0 ≤ t`
* `htΔt` – `t ≤ Δt`

## Conclusion
* for the matrices `T` returned, the curvature term is in `[F]` and the input term in `[G]`
-/

-- Authors:       Claude Opus 5.5
-- Written:       16-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.taylorMatricesFloat_outer (sys : LinearSys 𝕋 n) {Δt : 𝕋}
    (hΔt : 0 < toReal Δt) {m : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (htΔt : t ≤ toReal Δt) : -- --- CONCL ---
    ∀ T ∈ sys.taylorMatricesFloat Δt (m + 2),
    exp (t • toRealMat sys.A) - 1 - (t / toReal Δt) • (exp (toReal Δt • toRealMat sys.A) - 1)
        ∈ T.F.toSet ∧
      Real.MatExp.expIntegral (toRealMat sys.A) t
          - (t / toReal Δt) • Real.MatExp.expIntegral (toRealMat sys.A) (toReal Δt)
        ∈ T.G.toSet := by -- --- PROOF ---
  intro T hT
  rw [Option.mem_def] at hT
  simp only [LinearSys.taylorMatricesFloat, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at hT
  obtain ⟨s, hs, rfl⟩ := hT
  -- the halvings make the order `16` admissible, so `W` bounds the remainder
  have hadm := LinearSys.halvingsFloat_spec (η := 16) (by norm_num) s hs
  have hW := LinearSys.expRemainderMat_le_expRemainderSquaringFloat sys (m + 2) s hadm
  have hA : toRealMat sys.A ∈ (Interval.point sys.A).toSet := Interval.mem_point sys.A
  exact ⟨MatExp.expDiff_mem_intervalCorrectionMatrixTight _ hΔt _ hA hW ht0 htΔt,
    MatExp.expIntegralDiff_mem_intervalConstCorrectionMatrixTight _ hΔt _ _ hA hW ht0 htΔt⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
