module

public import CORALean.ContSet.PolyZonotope.Float.Definitions.SubsRel

@[expose] public section

/-!
# `subsMul` keeps the bracket

Each product term of the float lists has the exact product coefficient between its two directed
corner products (`Interval.mul_between_corners`), and the exponents add.

## Inputs
* `A` – first float term list
* `B` – second float term list
* `A'` – first real term list
* `B'` – second real term list

## Hypotheses
* `hA` – first lists are related
* `hB` – second lists are related

## Conclusion
* the product lists are related
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- If the float term lists `A`, `B` enclose the real lists `A'`, `B'` term by term (`subsRel`),
then the float product `subsMul A B` encloses the real product `subsMul A' B'` term by term. -/
theorem PolyZonotope.subsMul_rel {A B : List ((Interval 𝕋) × (Fin p → ℕ))}
    {A' B' : List (ℝ × (Fin p → ℕ))} (hA : PolyZonotope.subsRel A A')
    (hB : PolyZonotope.subsRel B B') : -- --- CONCL ---
    PolyZonotope.subsRel (PolyZonotope.subsMul A B)
      (Real.PolyZonotope.subsMul A' B') := by -- --- PROOF ---
  unfold PolyZonotope.subsRel at *
  induction hA with
  | nil => exact List.Forall₂.nil
  | cons hst _ ih =>
    rename_i s t _ _
    refine List.rel_append ?_ ih
    -- the row of one term of `A` against all of `B`
    clear ih
    induction hB with
    | nil => exact List.Forall₂.nil
    | cons hst' _ ih' =>
      refine List.Forall₂.cons ⟨?_, ?_⟩ ih'
      · simp only [hst.1, hst'.1]
      · have hb := Real.Interval.mul_between_corners hst.2.1 hst.2.2 hst'.2.1 hst'.2.2
        exact ⟨le_trans (Interval.mulLo_le _ _ _ _) hb.1, le_trans hb.2 (Interval.le_mulHi _ _ _ _)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
