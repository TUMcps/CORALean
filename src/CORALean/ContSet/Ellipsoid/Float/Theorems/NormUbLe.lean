module

public import CORALean.ContSet.Ellipsoid.Float.Operations.NormUb
public import CORALean.ContSet.Ellipsoid.Real.Theorems.NormUbLe
public import CORALean.ContSet.Ellipsoid.Float.Theorems.Basic

@[expose] public section

/-!
# The float `Ellipsoid.normUb` bounds every point's Euclidean norm

A point is `y + e` with `y` in the nominal ellipsoid, bounded by the exact layer's
`Ellipsoid.norm₂_le_normUb` against the stored floats, and `e` in the error box, bounded by the
length of its largest magnitudes. The roundings are all upward.

## Inputs
* `k` – Newton steps of the root
* `E` – ellipsoid
* `x` – point

## Hypotheses
* `hx` – `x` in `E`

## Conclusion
* the norm of `x` is at most `normUb`
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.norm₂_le_normUb (k : ℕ) (E : Ellipsoid 𝕋 n) {x : Vec ℝ n}
    (hx : x ∈ E.construct) : -- --- CONCL ---
    ‖x‖₂ ≤ toReal (E.normUb k) := by -- --- PROOF ---
  obtain ⟨y, hy, e, he, rfl⟩ := hx
  -- the nominal part, by the exact layer
  have hy' := CORALean.Real.Ellipsoid.norm₂_le_normUb _ hy
  -- the error box's largest magnitudes, and the rounded root of the floored trace
  set mg : Fin n → 𝕋 := fun i => maximum (absolute (E.I_error.inf i)) (absolute (E.I_error.sup i))
  set fr := sqrtUp k (sumUp fun i => maximum zero (E.Q i i))
  have herr : ∀ i, |e i| ≤ |toReal (mg i)| := by
    intro i
    have h : toReal (E.I_error.inf i) ≤ e i ∧ e i ≤ toReal (E.I_error.sup i) := he i
    have h' := abs_le_max_abs_abs h.1 h.2
    rw [toReal_maximum, toReal_absolute, toReal_absolute]
    exact le_trans h' (le_abs_self _)
  -- the error box, by the length of its largest magnitudes
  have hErr := norm₂_le_normUp k herr
  have hq : ‖toRealVec E.q‖₂ ≤ toReal (normUp k E.q) := norm₂_le_normUp k fun j => le_refl _
  -- the nominal trace is the stored one or `0`, at most the floored sum, rounded up
  have hF : Real.sqrt (InflatedContSet.nominal E).ellipsoid.Q.trace ≤ toReal fr := by
    refine le_trans (Real.sqrt_le_sqrt ?_) (le_sqrtUp k _)
    refine le_trans ?_ (sum_le_sumUp _)
    rw [Ellipsoid.nominal_Q_eq]
    split_ifs
    · exact Finset.sum_le_sum fun i _ => by
        rw [toReal_maximum, toReal_zero]
        exact le_max_right _ _
    · rw [Matrix.trace_zero]
      exact Finset.sum_nonneg fun i _ => by
        rw [toReal_maximum, toReal_zero]
        exact le_max_left _ _
  -- the two upward additions
  have s₁ := add_le_addUp (normUp k E.q) fr
  have s₂ := add_le_addUp (addUp (normUp k E.q) fr) (normUp k mg)
  have hnom :
      ‖y‖₂ ≤ ‖toRealVec E.q‖₂ + Real.sqrt (InflatedContSet.nominal E).ellipsoid.Q.trace := by
    have h := hy'
    rwa [CORALean.Real.Ellipsoid.normUb, E.nominal_q] at h
  show ‖y + e‖₂ ≤ toReal (addUp (addUp (normUp k E.q) fr) (normUp k mg))
  have := norm₂_add_le y e
  linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
