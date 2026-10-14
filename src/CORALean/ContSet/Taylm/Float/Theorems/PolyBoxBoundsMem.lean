module

public import CORALean.ContSet.Taylm.Float.Operations.Basic
public import CORALean.ContSet.Taylm.Float.Theorems.PowBoundsMem
public import CORALean.ContSet.Taylm.Float.Theorems.ProdBoundsMem
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil

@[expose] public section

/-!
# `Taylm.polyBoxBounds` brackets the polynomial

On a box `B` the polynomial of a term list lies in the stored range: each term by `prodBounds_mem`
and the corner products of the coefficient, the sum by the rounded list sums.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.polyBoxBounds_mem (L : List (𝕋 × (Fin n → ℕ))) {B : Fin n → Interval 𝕋} {t : Vec ℝ n}
    (ht : Taylm.InBox B t) :
    toReal (Taylm.polyBoxBounds L B).inf ≤ Real.Taylm.polyOf (L.map fun a => (toReal a.1, a.2)) t ∧
      Real.Taylm.polyOf (L.map fun a => (toReal a.1, a.2)) t
        ≤ toReal (Taylm.polyBoxBounds L B).sup := by -- --- PROOF ---
  -- one term
  have hterm : ∀ a : 𝕋 × (Fin n → ℕ),
      toReal (Taylm.termBoxBounds B a).inf ≤ toReal a.1 * Real.Taylm.monomial a.2 t ∧
        toReal a.1 * Real.Taylm.monomial a.2 t ≤ toReal (Taylm.termBoxBounds B a).sup := by
    intro a
    have hM := Taylm.prodBounds_mem (fun k => Taylm.powBounds (B k).inf (B k).sup (a.2 k))
      (fun k => t k ^ a.2 k) fun k => Taylm.powBounds_mem (ht k).1 (ht k).2 _
    exact Interval.mul_between_corners (le_refl _) (le_refl _) hM.1 hM.2
  -- the list sums, term by term
  induction L with
  | nil => simp [Taylm.polyBoxBounds, listSumDown, listSumUp, toReal_zero]
  | cons a L ih =>
    simp only [Taylm.polyBoxBounds, List.map_cons, listSumDown, listSumUp,
      Real.Taylm.polyOf_cons] at ih ⊢
    exact ⟨le_trans (addDown_le_add _ _) (add_le_add (hterm a).1 ih.1),
      le_trans (add_le_add (hterm a).2 ih.2) (add_le_addUp _ _)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
