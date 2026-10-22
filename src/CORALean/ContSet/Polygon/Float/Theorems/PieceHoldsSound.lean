module

public import CORALean.ContSet.Polygon.Float.Operations.PieceHolds
public import CORALean.ContSet.Polygon.Float.Theorems.OrientBoundsLe
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# A `true` from `Polygon.pieceHolds` is a point of the nominal piece

The triangle's barycentric coordinates (`Polygon.aux_inTriangle_sound`), put on its three vertices
and zero elsewhere, are the weights of a convex combination of the piece's vertices.

## Inputs
* `p` – V-polytope
* `x` – point of length `2`

## Hypotheses
* `h` – `Polygon.pieceHolds p x` holds

## Conclusion
* A `true` from `Polygon.pieceHolds` is a point of the nominal piece
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A `true` from `Polygon.inTriangle` is a convex combination. -/
theorem Polygon.aux_inTriangle_sound {a b c x : Vec 𝕋 2}
    (h : Polygon.inTriangle a b c x = true) : -- --- CONCL ---
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


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.pieceHolds_sound {p : VPolytope (Vec 𝕋 2)} {x : Vec 𝕋 2}
    (h : Polygon.pieceHolds p x = true) : -- --- CONCL ---
    toRealVec x ∈ nominalSet p := by -- --- PROOF ---
  simp only [Polygon.pieceHolds, List.any_eq_true, List.mem_finRange, true_and] at h
  obtain ⟨a, b, c, h⟩ := h
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, hx⟩ := Polygon.aux_inTriangle_sound h
  -- the weights, on the three corners
  let w : Fin p.k → ℝ := fun j =>
    (if j = a then α else 0) + (if j = b then β else 0) + (if j = c then γ else 0)
  refine ⟨w, fun j => ?_, ?_, ?_⟩
  · simp only [w]
    split_ifs <;> linarith
  · simp only [w, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact hsum
  · -- the combination is the point
    rw [hx]
    simp only [w, add_smul, ite_smul, zero_smul, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
