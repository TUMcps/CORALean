module

public import CORALean.ContDynamics.LinearSys.Operations.ExpRemainderSquaringFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpRemainderMat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalTaylorFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ExpMemExpSquaringFloat
public import CORALean.ContSet.Interval.Float.Theorems.SmulOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint

@[expose] public section

/-!
# `expRemainderSquaringFloat` bounds CORA's remainder `E(Δt,η)` from above

`e^{|A|Δt}` lies in the squarings when the halvings make the order `16` admissible, and the series
of `|A|Δt` lies in its Taylor box, so the upper end of the one less the lower end of the other,
rounded up, is over `E(Δt,η) = e^{|A|Δt} − Σ_{i≤η}(|A|Δt)ⁱ/i!`, entry by entry.

## Inputs
* `sys` – float linear system
* `Δt` – float step length
* `η` – Taylor order
* `s` – halvings
* `j` – row
* `k` – column

## Hypotheses
* `hs` – the order `16` is admissible for `|A|` at `Δt / 2^s`

## Conclusion
* the entry of `E(Δt,η)` is at most that of `expRemainderSquaringFloat`
-/

-- Authors:       Claude Opus 5.5
-- Written:       16-November-2026
-- Last update:   19-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.expRemainderMat_le_expRemainderSquaringFloat
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

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
