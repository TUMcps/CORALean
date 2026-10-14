module

public import CORALean.ContSet.Ellipsoid.Float.Operations.NormUb
public import CORALean.ContSet.Ellipsoid.Real.Theorems.NormUbLe

@[expose] public section

/-!
# The float `Ellipsoid.normUb` bounds every point's Euclidean norm

A point is `y + e` with `y` in the nominal ellipsoid, bounded by the exact layer's
`Ellipsoid.norm₂_le_normUb` against the stored floats, and `e` in the error box, bounded by the
length of its largest magnitudes. The roundings are all upward.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.norm₂_le_normUb (k : ℕ) (E : Ellipsoid 𝕋 n) {x : Vec ℝ n}
    (hx : x ∈ E.construct) : ‖x‖₂ ≤ toReal (E.normUb k) := by -- --- PROOF ---
  obtain ⟨y, hy, e, he, rfl⟩ := hx
  -- the nominal part, by the exact layer
  have hy' := CORALean.Real.Ellipsoid.norm₂_le_normUb _ hy
  -- the error box's largest magnitudes, and the rounded Frobenius norm of the generators
  set mg : Fin n → 𝕋 := fun i => maximum (absolute (E.I_error.inf i)) (absolute (E.I_error.sup i))
  set fr := sqrtUp k (sumUp fun i => sqSumUp fun j => absolute (E.G i j))
  have herr : ∀ i, |e i| ≤ |toReal (mg i)| := by
    intro i
    have h : toReal (E.I_error.inf i) ≤ e i ∧ e i ≤ toReal (E.I_error.sup i) := he i
    have h' := abs_le_max_abs_abs h.1 h.2
    rw [toReal_maximum, toReal_absolute, toReal_absolute]
    exact le_trans h' (le_abs_self _)
  -- the error box, by the length of its largest magnitudes
  have hErr := norm₂_le_normUp k herr
  have hq : ‖toRealVec E.c‖₂ ≤ toReal (normUp k E.c) := norm₂_le_normUp k fun j => le_refl _
  -- the Frobenius norm of the stored generator matrix, rounded up
  have hF : Real.sqrt (∑ i, ∑ j, toReal (E.G i j) ^ 2) ≤
      toReal fr := by
    refine le_trans (Real.sqrt_le_sqrt ?_) (le_sqrtUp k _)
    refine le_trans (Finset.sum_le_sum fun i _ => ?_) (sum_le_sumUp _)
    exact sq_sum_le_sqSumUp (v := fun j => toReal (E.G i j)) (m := fun j => absolute (E.G i j))
      fun j => by rw [toReal_absolute]
  -- the two upward additions
  have s₁ := add_le_addUp (normUp k E.c) fr
  have s₂ := add_le_addUp (addUp (normUp k E.c) fr) (normUp k mg)
  have hnom : ‖y‖₂ ≤ ‖toRealVec E.c‖₂ + Real.sqrt (∑ i, ∑ j, toReal (E.G i j) ^ 2) := hy'
  show ‖y + e‖₂ ≤ toReal (addUp (addUp (normUp k E.c) fr) (normUp k mg))
  have := norm₂_add_le y e
  linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
