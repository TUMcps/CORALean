module

public import CORALean.Global.EuclideanNorm
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-!
# A linear image of a zonotope from approximate images of its generators

[1, Thm. III.1] and [1, Thm. IV.1]: if a linear map `M` (`e^{At}`, resp. `∫₀^δ e^{At}dt`) is
known at the center and at each generator only up to an error box — `M c ∈ ĉ ⊕ [-1, 1]ⁿ e_c`,
`M gᵢ ∈ ĝᵢ ⊕ [-1, 1]ⁿ eᵢ`, Lemmas III.1 and IV.1 — then `M⟨c, g⟩ ⊆ ⟨ĉ, ĝ⟩ ⊕ [-1, 1]ⁿ(e_c + Σ eᵢ)`.
By linearity, `M(c + Σ βᵢgᵢ) = ĉ + Σ βᵢĝᵢ` plus an error at most `e_c + Σ |βᵢ| eᵢ` in each
coordinate. One error per vector, as Thm. IV.1 writes it: Thm. III.1's single `ε_norm` is
the case of equal `εᵢ`, `eᵢ = ‖gᵢ‖ ε t`. [1, Alg. 2] calls it in lines 1, 7 and 8.

## Inputs
* `M` – linear map
* `c` – zonotope center
* `g` – zonotope generators
* `chat` – approximate image of the center
* `ghat` – approximate images of the generators
* `ec` – center error
* `eg` – generator errors

## Hypotheses
* `hc` – center image error bounded
* `hg` – generator image errors bounded

## Conclusion
* the image lies in the approximating zonotope plus an error box

## References

* [1] M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the
  Krylov Subspace". IEEE Transactions on Automatic Control, 65(2):477-492, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Krylov.image_subset_of_approx (M : Mat ℝ n m) (c : Vec ℝ m) (g : Fin p → Vec ℝ m)
    (chat : Vec ℝ n) (ghat : Fin p → Vec ℝ n) (ec : ℝ) (eg : Fin p → ℝ)
    (hc : ∀ j, |(M *ᵥ c - chat) j| ≤ ec)
    (hg : ∀ i j, |(M *ᵥ g i - ghat i) j| ≤ eg i) : -- --- CONCL ---
    (M *ᵥ ·) '' {x | ∃ β : Fin p → ℝ, (∀ i, |β i| ≤ 1) ∧ x = c + ∑ i, β i • g i}
      ⊆ {y | ∃ β : Fin p → ℝ, (∀ i, |β i| ≤ 1) ∧ ∃ r : Vec ℝ n, (∀ j, |r j| ≤ ec + ∑ i, eg i) ∧
          y = chat + ∑ i, β i • ghat i + r} := by -- --- PROOF ---
  rintro _ ⟨x, ⟨β, hβ, rfl⟩, rfl⟩
  refine ⟨β, hβ, M *ᵥ (c + ∑ i, β i • g i) - (chat + ∑ i, β i • ghat i), fun j => ?_, by abel⟩
  -- the error splits into the center's and each generator's, scaled by `|βᵢ| ≤ 1`
  have hsplit : M *ᵥ (c + ∑ i, β i • g i) - (chat + ∑ i, β i • ghat i)
      = (M *ᵥ c - chat) + ∑ i, β i • (M *ᵥ g i - ghat i) := by
    rw [mulVec_add, mulVec_sum]
    simp only [mulVec_smul, smul_sub, Finset.sum_sub_distrib]
    abel
  rw [hsplit, Pi.add_apply, Finset.sum_apply]
  refine (abs_add_le _ _).trans (add_le_add (hc j) ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun i _ => ?_)))
  have heg : 0 ≤ eg i := (abs_nonneg _).trans (hg i j)
  rw [Pi.smul_apply, smul_eq_mul, abs_mul]
  calc |β i| * |(M *ᵥ g i - ghat i) j| ≤ 1 * eg i :=
        mul_le_mul (hβ i) (hg i j) (abs_nonneg _) zero_le_one
    _ = eg i := one_mul _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
