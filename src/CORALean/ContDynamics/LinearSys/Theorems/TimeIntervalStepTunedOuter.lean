module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormSmulLeNormUpperBoundFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TuneOrderSpecFloat
public import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint

@[expose] public section

/-!
# An enclosure whose order a computable search chose

`timeIntervalStep_outer_at` at the order `MatExp.tuneOrder` returns, the order selector of [1]:
the search runs at the float bound `MatExp.normUpperBound` of `[r, r] · A`, and its result is
admissible at the real scaled matrix (`tuneOrder_spec`, the bound reaching `‖r • A‖` by
`norm_smul_le_normUpperBound`), which is the side condition the outer theorem takes. So the
order is chosen by a computation rather than by `expRemainderOrder`'s infimum, and the
enclosure guarantee is the same.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float CORALean.Real
open Matrix ContSet NormedSpace SoundFloatArithmetic

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every image of the initial set under the flow, at every time of the step, with the order
returned by the computable search `tuneOrder` at the float norm bound of `[r, r] · A`. -/
theorem LinearSys.timeIntervalStep_outer_tuned (sys : LinearSys 𝕋 n) {r ε : 𝕋}
    (hr : 0 < toReal r) {fuel η : ℕ}
    (h : MatExp.tuneOrder (MatExp.normUpperBound (Interval.smul r r (Interval.point sys.A)))
      ε fuel = some η) (X₀ : S n) {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ toReal r) :
    (fun x₀ => exp (t • Scalar.toRealMat sys.A) *ᵥ x₀) '' construct X₀
      ⊆ construct (sys.timeIntervalStep (toReal r) η X₀) := by -- --- PROOF ---
  have hnorm := MatExp.norm_smul_le_normUpperBound (Interval.point sys.A) r
    (Interval.mem_point sys.A)
  obtain ⟨h2, -, hs⟩ := MatExp.tuneOrder_spec hnorm h
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, η = m + 2 := ⟨η - 2, by omega⟩
  exact sys.timeIntervalStep_outer_at hr hs X₀ ht0 htr

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
