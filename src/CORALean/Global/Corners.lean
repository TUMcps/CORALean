import CORALean.Global.Tensor
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Choosing one of two per coordinate

A box has `2ⁿ` corners, one per choice of end per coordinate, and any weighting
over those choices that is a product of per-coordinate factors behaves the same
way: the weights sum to the product of the per-coordinate sums, and weighting
them by a second such product leaves each coordinate's own average, since the
sum factors coordinate by coordinate. `sum_prod_bool_mul` is that at a second
product which is `1` away from one coordinate.

The facts are stated here rather than at the box, being about `Fin n → Bool`
and nothing else. `signEquiv` is the bookkeeping that lets a list indexed by
`Fin k` hold something indexed by those choices.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   12-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}

/-- Computable, and deliberately: the float layer stores a corner list and has
to be able to produce one. -/
def signEquiv (n : ℕ) : Fin (2 ^ n) ≃ (Fin n → Bool) :=
  finFunctionFinEquiv.symm.trans (Equiv.arrowCongr (Equiv.refl (Fin n)) finTwoEquiv)

theorem sum_prod_bool (f g : Fin n → ℝ) :
    ∑ σ : Fin n → Bool, ∏ j, (if σ j then f j else g j) = ∏ j, (f j + g j) := by
  rw [show (∏ j, (f j + g j)) = ∏ j, ∑ b : Bool, (if b then f j else g j) from
        Finset.prod_congr rfl fun j _ => by simp,
      Finset.prod_univ_sum, Fintype.piFinset_univ]

theorem sum_prod_bool_prod (t u v : Fin n → ℝ) :
    ∑ σ : Fin n → Bool,
        (∏ j, (if σ j then t j else 1 - t j)) * ∏ j, (if σ j then u j else v j)
      = ∏ j, (t j * u j + (1 - t j) * v j) := by -- --- PROOF ---
  -- the two products merge factor by factor, each factor taking the same side
  have key : ∀ σ : Fin n → Bool,
      (∏ j, (if σ j then t j else 1 - t j)) * ∏ j, (if σ j then u j else v j)
        = ∏ j, (if σ j then t j * u j else (1 - t j) * v j) := fun σ => by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => by cases hb : σ j <;> simp
  rw [Finset.sum_congr rfl fun σ (_ : σ ∈ (Finset.univ : Finset (Fin n → Bool))) => key σ,
    sum_prod_bool (fun j => t j * u j) fun j => (1 - t j) * v j]


-- =======================================  MAIN THEOREM  ======================================= --

theorem sum_prod_bool_mul (t u v : Fin n → ℝ) (i : Fin n) :
    ∑ σ : Fin n → Bool,
        (∏ j, (if σ j then t j else 1 - t j)) * (if σ i then u i else v i)
      = t i * u i + (1 - t i) * v i := by -- --- PROOF ---
  -- one coordinate's factor absorbs its endpoint; the rest are untouched
  have key : ∀ σ : Fin n → Bool,
      (∏ j, (if σ j then t j else 1 - t j)) * (if σ i then u i else v i)
        = ∏ j, (if σ j then (if j = i then t i * u i else t j)
                       else if j = i then (1 - t i) * v i else 1 - t j) := by
    intro σ
    have hsplitL := Finset.mul_prod_erase Finset.univ
      (fun j => if σ j then t j else 1 - t j) (Finset.mem_univ i)
    have hsplitR := Finset.mul_prod_erase Finset.univ
      (fun j => if σ j then (if j = i then t i * u i else t j)
                       else if j = i then (1 - t i) * v i else 1 - t j) (Finset.mem_univ i)
    -- every factor but `i`'s is unchanged, so only the split factor is compared
    have hrest : ∏ j ∈ Finset.univ.erase i,
          (if σ j then (if j = i then t i * u i else t j)
                  else if j = i then (1 - t i) * v i else 1 - t j)
        = ∏ j ∈ Finset.univ.erase i, (if σ j then t j else 1 - t j) :=
      Finset.prod_congr rfl fun j hj => by
        rw [if_neg (Finset.ne_of_mem_erase hj), if_neg (Finset.ne_of_mem_erase hj)]
    rw [← hsplitL, ← hsplitR, hrest]
    cases hb : σ i <;> simp <;> ring
  rw [Finset.sum_congr rfl fun σ _ => key σ, sum_prod_bool, Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    rw [if_neg hj, if_neg hj]
    ring
  · intro h
    exact absurd (Finset.mem_univ i) h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
