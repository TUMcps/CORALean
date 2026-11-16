module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalConstCorrectionMatrixTightFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalCorrectionMatrixTightFloat
public import CORALean.ContDynamics.LinearSys.Operations.TaylorMatricesFloat
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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `W` of `expRemainderSquaringFloat` is over `E(Δt,η)`, entry by entry. -/
private theorem LinearSys.aux_expRemainderMat_le_expRemainderSquaringFloat
    (sys : LinearSys 𝕋 n) {Δt : 𝕋} (η s : ℕ)
    (hs : ({ sys with A := Interval.magnitudeMat (Interval.point sys.A) } : LinearSys 𝕋 n)
      |>.IsOrderAdmissibleFloat (half^[s] Δt) (half^[s] Δt) 16)
    (j k : Fin n) : -- --- CONCL ---
    Real.MatExp.expRemainderMat (toRealMat sys.A) (toReal Δt) η j k
      ≤ toReal (sys.expRemainderSquaringFloat Δt η s j k) := by -- --- PROOF ---
  set M := Interval.magnitudeMat (Interval.point sys.A) with hM
  set B := Interval.smul Δt Δt (Interval.point M) with hB
  -- `|A|` is the real image of the float magnitude
  have e : toRealMat M = Real.MatExp.absMat (toRealMat sys.A) := by
    funext i j
    simp only [hM, toRealMat, Interval.magnitudeMat, toReal_maximum, toReal_absolute,
      Real.MatExp.absMat, Interval.point, max_self]
  have hAbs : Real.MatExp.absMat (toRealMat sys.A) ∈ (Interval.point M).toSet := by
    have h := Interval.mem_point M
    have e' : RealImage.realImage M = toRealMat M := rfl
    rwa [e', e] at h
  -- the scaled matrix is in the box, so the series is in the Taylor box
  have hmem : toReal Δt • Real.MatExp.absMat (toRealMat sys.A) ∈ B.toSet :=
    Interval.smul_outer le_rfl le_rfl _ hAbs
  have htay := Real.Interval.mem_mat_iff.mp (MatExp.expTaylor_mem_expIntervalTaylor B hmem η) j k
  -- the squarings hold the exponential of `|A|Δt`
  have hsq := Real.Interval.mem_mat_iff.mp
    (LinearSys.exp_mem_expSquaringFloat _ hs (t := toReal Δt) le_rfl le_rfl) j k
  simp only [Interval.nominal, RealImage.realImage, toRealMat] at htay hsq
  have hsub := sub_le_subUp
    ((({ sys with A := M } : LinearSys 𝕋 n).expSquaringFloat Δt Δt 16 s).sup j k)
    ((MatExp.expIntervalTaylor B η).inf j k)
  simp only [LinearSys.expRemainderSquaringFloat, ← hM, ← hB, Interval.materialiseMat_eq]
  simp only [Real.MatExp.expRemainderMat, Matrix.sub_apply]
  have e2 : Scalar.toRealMat M = Real.MatExp.absMat (toRealMat sys.A) := e
  rw [e2] at hsq
  linarith [hsq.2, htay.1]


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
  have hW := LinearSys.aux_expRemainderMat_le_expRemainderSquaringFloat sys (m + 2) s hadm
  have hA : toRealMat sys.A ∈ (Interval.point sys.A).toSet := Interval.mem_point sys.A
  exact ⟨MatExp.expDiff_mem_intervalCorrectionMatrixTight _ hΔt _ hA hW ht0 htΔt,
    MatExp.expIntegralDiff_mem_intervalConstCorrectionMatrixTight _ hΔt _ _ hA hW ht0 htΔt⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
