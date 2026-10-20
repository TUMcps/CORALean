module

public import CORALean.ContSet.Polygon.Float.Polygon
public import CORALean.ContSet.SetUnion.Theorems.Basic
public import CORALean.ContSet.VPolytope.Float.Operations.SupportBound

@[expose] public section

/-!
# `Polygon.boundDot`, over a floating-point scalar

CORA's `@polygon/supportFunc_` at `upper` as a `FloatBound`: the largest of the pieces' own
`VPolytope.boundDot` (each a rounded dot product per vertex plus the error box's reach), seeded
with the first piece's, so the bound of a polygon is not pulled up to `0`. A polygon without a piece
is empty, and then `zero` is as good a bound as any (CORA gives `-Inf`, outside `𝕋`).

## Inputs
* `P` – polygon
* `c` – center of length `2 →ₗ[ℝ] ℝ`
* `a` – vector of length `2`

## Hypotheses
* `hc` – `c` is the dot product with the stored vector `a`

## Output
* the float bound on `c` over `P`, the largest of the pieces' bounds
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem Polygon.aux_le_foldr_maximum (l : List 𝕋) (s : 𝕋) {a : 𝕋} (h : a ∈ l) :
    toReal a ≤ toReal (l.foldr maximum s) := by -- --- PROOF ---
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons b l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · rw [List.foldr_cons, toReal_maximum]; exact le_max_left _ _
    · rw [List.foldr_cons, toReal_maximum]; exact le_trans (ih h) (le_max_right _ _)


-- =====================================  MAIN DEFINITION  ====================================== --

def Polygon.boundDot (P : Polygon 𝕋) {c : Vec ℝ 2 →ₗ[ℝ] ℝ} (a : Vec 𝕋 2)
    (hc : ∀ x : Vec ℝ 2, c x = ∑ j, toReal (a j) * x j) :
    FloatBound 𝕋 (ContSet.construct P) c where
  val := (P.sets.map fun p => (p.boundDot a hc).val).foldr maximum
    ((P.sets.map fun p => (p.boundDot a hc).val).headD zero)
  le x hx := by
    obtain ⟨p, hp, hxp⟩ := SetUnion.mem_construct.mp hx
    exact le_trans ((p.boundDot a hc).le x hxp)
      (Polygon.aux_le_foldr_maximum _ _ (List.mem_map_of_mem hp))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
