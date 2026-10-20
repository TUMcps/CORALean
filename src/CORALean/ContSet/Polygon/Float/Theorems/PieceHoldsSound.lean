module

public import CORALean.ContSet.Polygon.Float.Operations.PieceHolds
public import CORALean.ContSet.Polygon.Float.Theorems.InTriangleSound

@[expose] public section

/-!
# A `true` from `Polygon.pieceHolds` is a point of the nominal piece

The triangle's barycentric coordinates (`Polygon.inTriangle_sound`), put on its three vertices
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


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.pieceHolds_sound {p : VPolytope (Vec 𝕋 2)} {x : Vec 𝕋 2}
    (h : Polygon.pieceHolds p x = true) : -- --- CONCL ---
    toRealVec x ∈ nominalSet p := by -- --- PROOF ---
  simp only [Polygon.pieceHolds, List.any_eq_true, List.mem_finRange, true_and] at h
  obtain ⟨a, b, c, h⟩ := h
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, hx⟩ := Polygon.inTriangle_sound h
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
