import CORALean.ContSet.PolyZonotope.Float.Theorems.SubsXprodRel
import CORALean.ContSet.PolyZonotope.Float.Operations.SubsTerms
import CORALean.ContSet.PolyZonotope.Real.Operations.SubsTerms

/-!
# `subsTerms` keeps the bracket

The generators are the `Xprod`s of the original generators in turn, each term tagged with its
generator.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.subsTerms_rel (pZ : PolyZonotope 𝕋 n) {nu : ℕ} (pZin : PolyZonotope 𝕋 nu)
    (idu : Fin nu → Fin pZ.p) :
    List.Forall₂ (fun s t => s.1 = t.1 ∧ s.2.2 = t.2.2 ∧ toReal s.2.1.1 ≤ t.2.1 ∧
        t.2.1 ≤ toReal s.2.1.2)
      (pZ.subsTerms pZin idu)
      (Real.PolyZonotope.subsTerms (InflatedContSet.nominal pZ)
        (InflatedContSet.nominal pZin) idu) := by -- --- PROOF ---
  unfold PolyZonotope.subsTerms Real.PolyZonotope.subsTerms
  generalize List.finRange pZ.h = L
  induction L with
  | nil => exact List.Forall₂.nil
  | cons i L ih =>
    rw [List.flatMap_cons, List.flatMap_cons]
    refine List.rel_append ?_ ih
    have hx := PolyZonotope.subsXprod_rel pZ pZin idu i
    unfold PolyZonotope.subsRel at hx
    generalize pZ.subsXprod pZin idu i = X at hx
    generalize Real.PolyZonotope.subsXprod (InflatedContSet.nominal pZ)
      (InflatedContSet.nominal pZin) idu i = X' at hx
    induction hx with
    | nil => exact List.Forall₂.nil
    | cons h _ ih' => exact List.Forall₂.cons ⟨rfl, h⟩ ih'

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
