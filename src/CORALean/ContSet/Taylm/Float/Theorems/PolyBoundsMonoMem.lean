module

public import CORALean.ContSet.Taylm.Float.Operations.PolyBoundsMono
public import CORALean.ContSet.Taylm.Float.Theorems.MonomialRangeMem
public import CORALean.ContSet.Taylm.Float.Theorems.SumRangesMem
public import CORALean.ContSet.Taylm.Float.Theorems.TimesZeroInfMem

@[expose] public section

/-!
# `Taylm.polyBoundsMono` holds the polynomial

## Inputs
* `L` – term list
* `t` – point of the box

## Hypotheses
* `ht` – `t` lies in the box `[-1, 1]ⁿ`

## Conclusion
* the polynomial of `L` at `t` lies in the bounds
-/

-- Authors:       Claude Opus 5.5
-- Written:       20-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.polyBoundsMono_mem (L : List (𝕋 × (Fin n → ℕ))) {t : Vec ℝ n}
    (ht : t ∈ Real.Taylm.box n) : -- --- CONCL ---
    toReal (Taylm.polyBoundsMono L).inf
        ≤ Real.Taylm.polyOf (L.map fun a => (toReal a.1, a.2)) t ∧
      Real.Taylm.polyOf (L.map fun a => (toReal a.1, a.2)) t
        ≤ toReal (Taylm.polyBoundsMono L).sup := by -- --- PROOF ---
  -- each term is its monomial's range times its coefficient
  have h := Taylm.sumRanges_mem
    (fun a : 𝕋 × (Fin n → ℕ) => Taylm.timesZeroInf (Taylm.monomialRange a.2) ⟨a.1, a.1⟩) L
    (fun a => Real.Taylm.monomial a.2 t * toReal a.1) (I := ⟨zero, zero⟩) (x := 0)
    (by simp [toReal_zero])
    (fun a _ => Taylm.timesZeroInf_mem (Taylm.monomialRange_mem ht a.2).1
      (Taylm.monomialRange_mem ht a.2).2 le_rfl le_rfl)
  have e : Real.Taylm.polyOf (L.map fun a => (toReal a.1, a.2)) t
      = 0 + (L.map fun a => Real.Taylm.monomial a.2 t * toReal a.1).sum := by
    simp only [Real.Taylm.polyOf, List.map_map, Function.comp_def, zero_add]
    congr 1
    exact List.map_congr_left fun a _ => mul_comm _ _
  rw [e]
  exact h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
