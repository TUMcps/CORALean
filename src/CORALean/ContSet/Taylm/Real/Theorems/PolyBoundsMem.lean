module

public import CORALean.ContSet.Taylm.Real.Operations.PolyBounds
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import CORALean.ContSet.Taylm.Real.Theorems.TermBoundsMem

@[expose] public section

/-!
# A term list stays in `polyBounds` on the box

## Inputs
* `L` – terms of the polynomial
* `t` – point

## Hypotheses
* `ht` – point lies in the unit box

## Conclusion
* the polynomial's value lies in its bounds
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.polyBounds_mem (L : List (ℝ × (Fin n → ℕ))) {t : Vec ℝ n}
    (ht : t ∈ Taylm.box n) : -- --- CONCL ---
    (Taylm.polyBounds L).inf ≤ Taylm.polyOf L t ∧
      Taylm.polyOf L t ≤ (Taylm.polyBounds L).sup := by -- --- PROOF ---
  induction L with
  | nil => simp [Taylm.polyBounds]
  | cons a L ih =>
    have := Taylm.termBounds_mem a ht
    simp only [Taylm.polyBounds, List.map_cons, List.sum_cons, Taylm.polyOf_cons] at *
    constructor <;> linarith [ih.1, ih.2, this.1, this.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
