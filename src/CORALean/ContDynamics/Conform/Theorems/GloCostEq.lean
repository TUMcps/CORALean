module

public import CORALean.ContDynamics.Conform.Theorems.IntervalNormSmul
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# [1, Lemma 2]: the cost is linear in the stretch factors

With `r(Ŷ) = ‖Ȳ‖_I` and `Ȳ`'s generators from [1, Lemma 1], the cost (4a) is
`γ α` with `γ = ∑ₘ ∑ₖ wₖ 1^T [|C̄ G_x|, ∑ᵢ |D̄ᵢ G_u|]` (17), for `α ≥ 0`. Stated with
the bracket applied to `α` blockwise, per test case `m` and step `k`; `C̄` and `D̄` are the
test case's GLO matrices, `k` running below the test-case length `n_k`. This is the
objective of [1, Alg. 1]'s program, the cost half of [1, Thm. 2].

## References

* [1] L. Lützow and M. Althoff. "Reachset-Conformant System Identification". IEEE
      Transactions on Automatic Control, 71(5):3014-3029, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n p q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 2]: `∑ₘ ∑ₖ wₖ ‖Ȳₖ⁽ᵐ⁾‖_I = γ α`, `γ` from (17). -/
theorem Conform.gloCost_eq {M ιx ιu : Type} [Fintype M] [Fintype ιx] [Fintype ιu]
    (Cb : M → ℕ → Mat ℝ q n) (Db : M → (k : ℕ) → Fin (k + 1) → Mat ℝ q p)
    (Gx : ιx → Vec ℝ n) (αx : ιx → ℝ) (Gu : ιu → Vec ℝ p) (αu : ιu → ℝ)
    (hαx : ∀ j, 0 ≤ αx j) (hαu : ∀ l, 0 ≤ αu l) (w : ℕ → ℝ) (nk : ℕ) :
    ∑ m, ∑ k ∈ Finset.range nk, w k * Conform.intervalNorm (fun _ => 1)
        (fun j => Sum.elim αx (fun r : Fin (k + 1) × ιu => αu r.2) j
          • Sum.elim (fun j => Cb m k *ᵥ Gx j) (fun r : Fin (k + 1) × ιu => Db m k r.1 *ᵥ Gu r.2) j)
      = ∑ m, ∑ k ∈ Finset.range nk, w k * (∑ j, (∑ a, |(Cb m k *ᵥ Gx j) a|) * αx j
          + ∑ l, (∑ i : Fin (k + 1), ∑ a, |(Db m k i *ᵥ Gu l) a|) * αu l) := by -- --- PROOF ---
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
  rw [Conform.intervalNorm_smul _ _ _ fun j => by rcases j with x | r <;> simp [hαx, hαu]]
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type,
    Finset.sum_mul, one_mul]
  rw [Finset.sum_comm (s := Finset.univ (α := Fin (k + 1)))]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
