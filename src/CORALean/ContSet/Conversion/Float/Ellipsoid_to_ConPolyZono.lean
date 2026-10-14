module

public import CORALean.ContSet.Conversion.Real.Ellipsoid_to_ConPolyZono
public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
public import CORALean.ContSet.Ellipsoid.Float.Ellipsoid
public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
public import CORALean.ContSet.Conversion.Float.Operations.Ellipsoid_to_ConPolyZono

@[expose] public section

/-!
# An ellipsoid as a constrained polynomial zonotope, over a floating-point scalar

The exact layer's construction with `one` and `neg (half one)` as the constraint entries and the
point `half one` as the right-hand side, all stored exactly; the centre and the generators are
copied and the error box is carried over: nothing rounds, so nothing is paid.

Not routed through the exact layer's set but through its *nominal* reading, which is the exact
conversion of the ellipsoid the stored floats describe, and that shares the exactness proof.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

variable [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The stored fields read as the exact layer's conversion of the nominal ellipsoid. -/
theorem Ellipsoid.aux_nominal_conPolyZono (E : Ellipsoid 𝕋 n) :
    nominal E.conPolyZono = Real.Ellipsoid.conPolyZono (nominal E) := by -- --- PROOF ---
  have hhalf : toReal (half (one : 𝕋)) = 1 / 2 := by rw [toReal_half, toReal_one]
  -- the fields agree entrywise
  show Real.ConPolyZono.mk _ _ _ _ _ _ _ _ _ _ _ _ = _
  simp only [Real.Ellipsoid.conPolyZono]
  congr 1
  case e_GI => funext l i; exact l.elim0
  case e_A =>
    funext i j
    change toReal (if j.val < E.k then (one : 𝕋) else neg (half one))
      = if j.val < E.k then (1 : ℝ) else -(1 / 2)
    split_ifs
    · exact toReal_one
    · rw [toReal_neg, hhalf]
  case e_b =>
    simp only [Interval.nominal, RealImage.realImage, Real.Interval.point]
    congr 1 <;> funext i <;> exact hhalf


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.conPolyZono_contains (E : Ellipsoid 𝕋 n) :
    E.construct ⊆ E.conPolyZono.construct := by -- --- PROOF ---
  -- the box is carried over, so only the nominal parts are compared
  refine mono_subset (fun x hx => ?_) subset_rfl
  have h := (Real.Ellipsoid.conPolyZono_exact (nominal E)).subset hx
  rw [← Ellipsoid.aux_nominal_conPolyZono] at h
  exact h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
