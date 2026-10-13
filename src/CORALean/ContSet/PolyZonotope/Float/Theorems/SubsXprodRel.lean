import CORALean.ContSet.PolyZonotope.Float.Theorems.SubsPowRel
import CORALean.ContSet.PolyZonotope.Float.Theorems.SubsPolyRel
import CORALean.ContSet.PolyZonotope.Float.Operations.SubsXprod
import CORALean.ContSet.PolyZonotope.Real.Operations.SubsXprod

/-!
# `subsXprod` keeps the bracket

The fold over the outputs multiplies the powers of the output polynomials (`subsPow_rel`,
`subsPoly_rel`), starting from `1`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.subsXprod_rel (pZ : PolyZonotope (Vec 𝕋 n)) {nu : ℕ}
    (pZin : PolyZonotope (Vec 𝕋 nu))
    (idu : Fin nu → Fin pZ.p) (i : Fin pZ.h) :
    PolyZonotope.subsRel (pZ.subsXprod pZin idu i)
      (Real.PolyZonotope.subsXprod (InflatedContSet.nominal pZ)
        (InflatedContSet.nominal pZin) idu i) := by -- --- PROOF ---
  unfold PolyZonotope.subsXprod Real.PolyZonotope.subsXprod
  generalize List.finRange nu = L
  have h1 : PolyZonotope.subsRel ([((one, one), 0)] : List ((𝕋 × 𝕋) × (Fin pZin.p → ℕ)))
      [(1, 0)] := List.Forall₂.cons ⟨rfl, by simp [toReal_one]⟩ List.Forall₂.nil
  generalize ([((one, one), 0)] : List ((𝕋 × 𝕋) × (Fin pZin.p → ℕ))) = acc at h1 ⊢
  generalize ([(1, 0)] : List (ℝ × (Fin pZin.p → ℕ))) = acc' at h1 ⊢
  induction L generalizing acc acc' with
  | nil => exact h1
  | cons ii L ih =>
    exact ih _ _ (PolyZonotope.subsMul_rel h1
      (PolyZonotope.subsPow_rel (PolyZonotope.subsPoly_rel pZin ii) _))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
