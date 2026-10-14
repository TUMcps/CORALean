module

public import CORALean.ContSet.ConZonotope.Float.ConZonotope
public import CORALean.ContSet.Interval.Float.Operations.Point

@[expose] public section

/-!
# A constrained zonotope whose error box is the point `0` is its nominal part

The error box adds `e` with `0 ≤ e ≤ 0` to a point of the nominal part, which is the point
itself. This is what an operation that keeps its nominal part exact and drops the box returns,
and what lets its guarantee be read off the coefficients.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.construct_eq_nominal {cZ : ConZonotope 𝕋 (Vec 𝕋 n)}
    (hE : cZ.I_error = Interval.point fun _ => zero) : cZ.construct = nominalSet cZ
      := by -- --- PROOF ---
  ext x
  constructor
  · rintro ⟨y, hy, e, he, rfl⟩
    -- the error is the point `0`
    have he0 : e = 0 := funext fun i => by
      have h : toReal (cZ.I_error.inf i) ≤ e i ∧ e i ≤ toReal (cZ.I_error.sup i) := he i
      rw [hE] at h
      change toReal (zero : 𝕋) ≤ e i ∧ e i ≤ toReal (zero : 𝕋) at h
      rw [toReal_zero] at h
      exact le_antisymm h.2 h.1
    subst he0
    show y + 0 ∈ nominalSet cZ
    rw [add_zero]
    exact hy
  · intro hx
    refine ⟨x, hx, 0, fun i => ?_, add_zero x⟩
    show toReal (cZ.I_error.inf i) ≤ 0 ∧ 0 ≤ toReal (cZ.I_error.sup i)
    rw [hE]
    change toReal (zero : 𝕋) ≤ 0 ∧ 0 ≤ toReal (zero : 𝕋)
    rw [toReal_zero]
    exact ⟨le_rfl, le_rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
