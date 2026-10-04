import CORALean.ContSet.Polygon.Float.Operations.InTriangle
import CORALean.ContSet.Polygon.Float.Theorems.OrientBoundsLe
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases

/-!
# A `true` from `Polygon.inTriangle` is a convex combination

The certified orientations, read as reals, are the triangle's `D > 0` and the point's three
edge orientations, all nonnegative; divided by `D` they are barycentric coordinates: nonnegative,
summing to `1` (the three orientations add up to `D`), and combining the corners to the point.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.inTriangle_sound {a b c x : Vec 𝕋 2} (h : Polygon.inTriangle a b c x = true) :
    ∃ α β γ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α + β + γ = 1 ∧
      toRealVec x = α • toRealVec a + β • toRealVec b + γ • toRealVec c := by -- --- PROOF ---
  simp only [Polygon.inTriangle, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hD, ha⟩, hb⟩, hc⟩ := h
  -- the four orientations, read as reals, on their certified sides of zero
  have eD := lt_of_lt_of_le (toReal_zero.symm.trans_lt (toReal_lt_of_ltStrict hD))
    (Polygon.orientBounds_le a b c).1
  have ea := le_trans (toReal_zero.symm.trans_le (toReal_le_of_le ha))
    (Polygon.orientBounds_le b c x).1
  have eb := le_trans (toReal_zero.symm.trans_le (toReal_le_of_le hb))
    (Polygon.orientBounds_le c a x).1
  have ec := le_trans (toReal_zero.symm.trans_le (toReal_le_of_le hc))
    (Polygon.orientBounds_le a b x).1
  -- the barycentric coordinates
  set A₀ := toReal (a 0)
  set A₁ := toReal (a 1)
  set B₀ := toReal (b 0)
  set B₁ := toReal (b 1)
  set C₀ := toReal (c 0)
  set C₁ := toReal (c 1)
  set X₀ := toReal (x 0)
  set X₁ := toReal (x 1)
  set D := (B₀ - A₀) * (C₁ - A₁) - (B₁ - A₁) * (C₀ - A₀)
  have hD0 : D ≠ 0 := ne_of_gt eD
  refine ⟨((C₀ - B₀) * (X₁ - B₁) - (C₁ - B₁) * (X₀ - B₀)) / D,
    ((A₀ - C₀) * (X₁ - C₁) - (A₁ - C₁) * (X₀ - C₀)) / D,
    ((B₀ - A₀) * (X₁ - A₁) - (B₁ - A₁) * (X₀ - A₀)) / D,
    div_nonneg ea eD.le, div_nonneg eb eD.le, div_nonneg ec eD.le, ?_, ?_⟩
  · -- the three edge orientations add up to the triangle's
    field_simp
    ring
  · -- and they combine the corners to the point, coordinate by coordinate
    funext i
    fin_cases i <;>
      simp only [toRealVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.zero_eta,
        Fin.mk_one] <;> field_simp <;> ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
