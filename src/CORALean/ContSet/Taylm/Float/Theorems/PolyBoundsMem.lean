module

public import CORALean.ContSet.Taylm.Float.Operations.Basic
public import CORALean.ContSet.Taylm.Float.Theorems.ToRealTermBounds
public import CORALean.ContSet.Taylm.Real.Theorems.PolyBoundsMem
public import CORALean.Global.Float.ListSum

@[expose] public section

/-!
# A term list stays in its float `polyBounds` on the box

The exact range, its two sums rounded outward.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.polyBounds_mem (L : List (𝕋 × (Fin n → ℕ))) {t : Vec ℝ n}
    (ht : t ∈ Real.Taylm.box n) :
    toReal (Taylm.polyBounds L).1 ≤ Real.Taylm.polyOf (L.map fun a => (toReal a.1, a.2)) t ∧
      Real.Taylm.polyOf (L.map fun a => (toReal a.1, a.2)) t
        ≤ toReal (Taylm.polyBounds L).2 := by -- --- PROOF ---
  have hr := Real.Taylm.polyBounds_mem (L.map fun a => (toReal a.1, a.2)) ht
  -- the exact sums are the float sums' terms read as reals
  have e1 : (Real.Taylm.polyBounds (L.map fun a => (toReal a.1, a.2))).1
      = ((L.map fun a => (Taylm.termBounds a).1).map toReal).sum := by
    simp only [Real.Taylm.polyBounds, List.map_map]
    congr 1
    exact List.map_congr_left fun a _ => by
      simp only [Function.comp_apply, ← Taylm.toReal_termBounds a]
  have e2 : (Real.Taylm.polyBounds (L.map fun a => (toReal a.1, a.2))).2
      = ((L.map fun a => (Taylm.termBounds a).2).map toReal).sum := by
    simp only [Real.Taylm.polyBounds, List.map_map]
    congr 1
    exact List.map_congr_left fun a _ => by
      simp only [Function.comp_apply, ← Taylm.toReal_termBounds a]
  rw [e1, e2] at hr
  exact ⟨le_trans (listSumDown_le _) hr.1, le_trans hr.2 (sum_le_listSumUp _)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
