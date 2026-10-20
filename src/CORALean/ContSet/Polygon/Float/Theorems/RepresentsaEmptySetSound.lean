module

public import CORALean.ContSet.Polygon.Float.Operations.RepresentsaEmptySet
public import CORALean.ContSet.SetUnion.Theorems.Basic

@[expose] public section

/-!
# `Polygon.representsaEmptySet` is sound

A piece with no vertex has an empty nominal polytope, so the piece, its sum with the error box, is
empty. Only this direction: a piece with vertices whose error box is empty is empty too, and the
test says `false` of it.

## Inputs
* `P` – polygon

## Hypotheses
* `h` – `Polygon.representsaEmptySet P` holds

## Conclusion
* the region of `P` is empty
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.representsaEmptySet_sound (P : Polygon 𝕋)
    (h : Polygon.representsaEmptySet P = true) : ContSet.construct P = ∅ := by -- --- PROOF ---
  simp only [Polygon.representsaEmptySet, List.all_eq_true, beq_iff_eq] at h
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  obtain ⟨p, hp, y, hy, e, he, rfl⟩ := SetUnion.mem_construct.mp hx
  have hk : p.k = 0 := h p hp
  have : y ∈ (Real.VPolytope.construct (InflatedContSet.nominal p)) := hy
  obtain ⟨β, -, hsum, -⟩ := this
  have hs : IsEmpty (Fin (InflatedContSet.nominal p).k) := ⟨fun j => by
    have hj : j.val < p.k := j.2
    omega⟩
  rw [Finset.univ_eq_empty, Finset.sum_empty] at hsum
  exact zero_ne_one hsum

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
