module

public import CORALean.ContSet.PolyZonotope.Float.Operations.MatGeneratorError

@[expose] public section

/-!
# Membership in the error box of a family of matrix generators

`mem_generatorError`'s counterpart at `Mat 𝕋 n m`: a combination of matrices bounded entrywise
by the generators, with coefficients in `[-1, 1]`, lies in the box. Entry `(i, j)` is
`abs_sum_le_radius` at row `j` of the generators' `(i, ·)` rows.

## Inputs
* `G` – family of matrix generators
* `Δ` – family of real error matrices
* `t` – coefficients

## Hypotheses
* `hG` – errors are bounded by the generators
* `ht` – coefficients are at most one

## Conclusion
* the weighted error sum lies in the error box
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m h : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.mem_matGeneratorError {G : Fin h → Mat 𝕋 n m} {Δ : Fin h → Mat ℝ n m}
    {t : Fin h → ℝ} (hG : ∀ l i j, |Δ l i j| ≤ |toReal (G l i j)|) (ht : ∀ l, |t l| ≤ 1) :
    ∑ l, t l • Δ l ∈ (PolyZonotope.matGeneratorError G).construct := by -- --- PROOF ---
  rintro ⟨i, j⟩
  -- entry `(i, j)` of the combination, the scalar on the right
  have he : Entrywise.entry (∑ l, t l • Δ l) (i, j) = ∑ l, Δ l i j * t l := by
    rw [Entrywise.entry_sum]
    exact Finset.sum_congr rfl fun l _ => by
      rw [Entrywise.entry_smul, Entrywise.entry_mat, mul_comm]
  have key := abs_sum_le_radius (d := fun j' l => G l i j') (Δ := fun j' l => Δ l i j')
    (fun j' l => hG l i j') ht j
  -- the box at `(i, j)` is symmetric about zero
  show toReal (neg (radius (fun j' l => G l i j') j)) ≤ Entrywise.entry (∑ l, t l • Δ l) (i, j)
    ∧ Entrywise.entry (∑ l, t l • Δ l) (i, j) ≤ toReal (radius (fun j' l => G l i j') j)
  rw [he, toReal_neg]
  exact ⟨neg_le_of_abs_le key, le_of_abs_le key⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
