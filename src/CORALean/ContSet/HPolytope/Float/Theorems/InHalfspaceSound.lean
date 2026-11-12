module

public import CORALean.ContSet.HPolytope.Float.Operations.InHalfspace
public import CORALean.ContSet.HPolytope.Float.Theorems.RowsOfMemToSet
public import CORALean.ContSet.HPolytope.Float.Theorems.Basic

@[expose] public section

/-!
# `HPolytope.inHalfspace` is sound

A certified row `a` with bound `bU ≤ γ` gives `a·x ≤ (A x)ᵢ ≤ bUᵢ ≤ γ` for every point of the
polytope (`HPolytope.rows_of_mem_toSet`), slacks and error box included.

## Inputs
* `P` – polytope
* `a` – normal
* `γ` – offset
* `x` – point

## Hypotheses
* `h` – the test passed
* `hx` – the point lies in `P`

## Conclusion
* `x·a ≤ γ`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.inHalfspace_sound {P : HPolytope 𝕋 (Vec 𝕋 n)} {a : Vec 𝕋 n} {γ : 𝕋}
    (h : P.inHalfspace a γ = true) {x : Vec ℝ n} (hx : x ∈ P.toSet) : -- --- CONCL ---
    x ⬝ᵥ toRealVec a ≤ toReal γ := by -- --- PROOF ---
  obtain ⟨i, -, hi⟩ := List.any_eq_true.mp h
  rw [Bool.and_eq_true] at hi
  have hrow := (HPolytope.rows_of_mem_toSet hx).1 i
  have heq : (toRealMat P.A *ᵥ x) i = x ⬝ᵥ toRealVec a := by
    rw [Matrix.mulVec, dotProduct_comm]
    exact Finset.sum_congr rfl fun j _ => by
      have := HPolytope.toReal_eq_of_eqVec hi.1 j
      show x j * toReal (P.A i j) = x j * toReal (a j)
      rw [this]
  rw [← heq]
  exact le_trans hrow (toReal_le_of_le hi.2)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
