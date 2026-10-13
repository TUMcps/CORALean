import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order

/-!
# The trace criterion has its optimum in closed form

[1, Sec. II-B]: minimising the sum of the squared semi-axes instead of the volume, that is
`trace Q(β) = (1 + 1/β) trace Q₁ + (1 + β) trace Q₂`, the optimal `β` is
`√(trace Q₁ / trace Q₂)`. With `t₁ = t₂ r²` the objective is
`t₁ + t₂ + t₂ (r²/β + β)`, and `r²/β + β − 2r = (r − β)²/β ≥ 0`.

## References

* [1] A. Halder. "On the parameterized computation of minimum volume outer ellipsoid of
      Minkowski sum of ellipsoids". In Proc. of the 57th IEEE Conference on Decision and
      Control (CDC), pp. 4040-4045, 2018. arXiv:1803.08157.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : Type*} [Fintype n]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. II-B]: `trace Q(β)` is minimal at `β = √(trace Q₁ / trace Q₂)`. -/
theorem Ellipsoid.halder_trace_isMinOn {Q₁ Q₂ : Matrix n n ℝ} (h₁ : 0 < Q₁.trace)
    (h₂ : 0 < Q₂.trace) :
    IsMinOn (fun β : ℝ => ((1 + 1 / β) • Q₁ + (1 + β) • Q₂).trace) (Set.Ioi 0)
      (Real.sqrt (Q₁.trace / Q₂.trace)) := by -- --- PROOF ---
  intro β hβ
  have hβ : 0 < β := hβ
  set r := Real.sqrt (Q₁.trace / Q₂.trace) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 (div_pos h₁ h₂)
  -- `t₁ = t₂ r²`
  have ht : Q₁.trace = Q₂.trace * r ^ 2 := by
    rw [hr, Real.sq_sqrt (div_pos h₁ h₂).le]; field_simp
  simp only [Set.mem_setOf_eq, trace_add, trace_smul, smul_eq_mul]
  rw [ht]
  -- the difference is `t₂ (r − β)² / β ≥ 0`
  have key : (1 + 1 / β) * (Q₂.trace * r ^ 2) + (1 + β) * Q₂.trace
      - ((1 + 1 / r) * (Q₂.trace * r ^ 2) + (1 + r) * Q₂.trace)
      = Q₂.trace * (r - β) ^ 2 / β := by
    field_simp; ring
  have h0 : 0 ≤ Q₂.trace * (r - β) ^ 2 / β := by positivity
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
