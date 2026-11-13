module

public import CORALean.ContDynamics.LinearSys.Operations.ClosedFormMatricesFloat
public import CORALean.ContSet.Interval.Float.Theorems.Basic

@[expose] public section

/-!
# What `closedFormMatricesFloat` formed

The matrices of the closed-form step are stored as arrays, which changes no value
(`Interval.materialiseMat_eq`): the order `ηe` the exponential was enclosed at, `W` the entrywise
remainder at it, `[e^{AΔt}]` the squaring of its enclosure after some `s` halvings, and `[F]` and
`[G]` the correction matrices at `ηe` and `W`.

## Inputs
* `sys` – linear system
* `Δt` – float step length
* `η` – Taylor order

## Hypotheses
* none; the claim is about every `M` the matrices form

## Conclusion
* the order, the remainder and the three interval matrices, as the step's theorems read them
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

omit [SoundFloatArithmetic 𝕋] in
/-- The fields of the matrices are the order, the remainder and the interval matrices the step
computes. -/
theorem LinearSys.closedFormMatricesFloat_spec
    {sys : LinearSys 𝕋 n} {Δt : 𝕋} {η : ℕ} : -- --- CONCL ---
    ∀ M ∈ sys.closedFormMatricesFloat Δt η,
    MatExp.admissibleOrder (MatExp.normUpperBound (Interval.smul Δt Δt
      (Interval.point (Interval.magnitudeMat (Interval.point sys.A))))) η MatExp.expEnclosureFuel
        = some M.ηe ∧ M.W = MatExp.expRemainderEntrywise sys.A Δt M.ηe M.ηe ∧
    ∃ s, sys.halvingsFloat Δt = some s ∧ M.eAdt = sys.expSquaringFloat Δt Δt 16 s ∧
      M.F = MatExp.intervalCorrectionMatrixEntrywise (Interval.point sys.A) Δt M.ηe M.W ∧
      M.G = MatExp.intervalConstCorrectionMatrixEntrywise (Interval.point sys.A) Δt M.ηe
        M.W := by -- --- PROOF ---
  intro M h
  -- the matrices are the fields of the structure `closedFormMatricesFloat` builds
  rw [Option.mem_def] at h
  unfold LinearSys.closedFormMatricesFloat at h
  dsimp only at h
  cases hop : MatExp.admissibleOrder (MatExp.normUpperBound (Interval.smul Δt Δt
      (Interval.point (Interval.magnitudeMat (Interval.point sys.A))))) η
      MatExp.expEnclosureFuel with
  | none => rw [hop] at h; exact absurd h (by simp)
  | some ηe =>
  rw [hop] at h
  cases hs : sys.halvingsFloat Δt with
  | none => simp only [hs, Bind.bind, Option.bind] at h; exact absurd h (by simp)
  | some s =>
  simp only [hs, Bind.bind, Option.bind, Pure.pure, Option.some.injEq] at h
  subst h
  refine ⟨rfl, ?_, s, rfl, ?_, ?_, ?_⟩
  · simp only [Interval.materialiseMat_eq]; rfl
  · simp only [Interval.materialiseMat_eq]
  · simp only [Interval.materialiseMat_eq]
  · simp only [Interval.materialiseMat_eq]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
