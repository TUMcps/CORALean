import CORALean.Arithmetic.Float.ContSet.Zonotope.Proofs.ReduceByOuterRefines

/-!
# `Zonotope.reduceBy` keeps the set it had

Nothing is argued twice: the exact layer already showed that boxing what a
partition drops over-approximates, and `reduceBy_outer_refines` that rounding the
block up only enlarges the result. Composing them gives the nominal inclusion,
and the box is untouched, hence `mono_subset`.

Soundness holds for every partition, exactly as over ℝ; a selection rule still
carries no proof obligation.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Float.Zonotope.Proofs

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet
open CORALean.Arithmetic.Real.Zonotope.Proofs

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n h q r : ℕ}

/-- What the absorbed generators contribute, so what the block must cover. -/
theorem abs_absorbed_le_radius (Z : Zonotope 𝕋 n)
    (part : Split (Fin Z.h) into (Fin q) and (Fin r)) {β : Vec ℝ Z.h}
    (hβ : ∀ j, |β j| ≤ 1) (i : Fin n) :
    |∑ l, toReal (Z.G i (part.right l)) * β (part.right l)|
      ≤ toReal (radius (fun i l => Z.G i (part.right l)) i) := by
  exact abs_sum_le_radius (d := fun i l => Z.G i (part.right l))
    (fun _ _ => le_refl _) (fun l => hβ (part.right l)) i

theorem reduceBy_nominal (Z : Zonotope 𝕋 n)
    (part : Split (Fin Z.h) into (Fin q) and (Fin r)) :
    nominalSet Z ⊆ nominalSet (Z.reduceBy part) :=
  subset_trans (CORALean.Arithmetic.Real.Zonotope.Proofs.reduceBy_outer (nominal Z) part)
    (reduceBy_outer_refines Z part)

theorem reduceBy_outer (Z : Zonotope 𝕋 n)
    (part : Split (Fin Z.h) into (Fin q) and (Fin r)) :
    Z.construct ⊆ (Z.reduceBy part).construct :=
  mono_subset (reduceBy_nominal Z part) (subset_refl _)

end CORALean.Arithmetic.Float.Zonotope.Proofs
