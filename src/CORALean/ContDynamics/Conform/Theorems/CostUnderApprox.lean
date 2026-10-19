module

public import CORALean.ContDynamics.Conform.Definitions.TemplateZono
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Order.CompleteLattice.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# [1, Prop. 1]: a cost below the program's, computable without solving it

`ℓ_U = ∑ₘ ∑ₖ wₖ 1^T maxₛ |y_a⁽ᵐ'ˢ⁾ₖ - y_Δ⁽ᵐ⁾ₖ|` (24) is at most `γ α` at every feasible
point of (22) in [1, Lemma 4]'s form, `wₖ ≥ 0`: `|Q_β β| ≤ |Q_β| |β| ≤ |Q_β| R_α α`
entrywise, and `1^T |Q_β| R_α α` is the step's share of `γ α` (17). So it bounds the
optimum from below. `y_Δ` is `[C̄, ∑ᵢ D̄ᵢ] B̃_c c_Δ`; at a point meeting (22d)
(`B_c c_Δ = 0`, `B_c` diagonal with entries in `{0, 1}`, `B_c = I` for nonlinear models)
`B̃_c c_Δ = c_Δ`, which is the form used here. The executions are indexed by `Fin (n_s + 1)`,
so that the maximum is over a nonempty set.

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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `|Q β|ₐ ≤ ∑ⱼ |Qₐⱼ| ρⱼ` when `|βⱼ| ≤ ρⱼ`. -/
theorem aux_abs_comb_le {m : ℕ} {ι : Type} [Fintype ι] (G : ι → Vec ℝ m) (β ρ : ι → ℝ)
    (hβ : ∀ j, |β j| ≤ ρ j) (a : Fin m) :
    |(∑ j, β j • G j) a| ≤ ∑ j, |G j a| * ρ j := by -- --- PROOF ---
  rw [Finset.sum_apply]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left (hβ j) (abs_nonneg _)


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 1]: `ℓ_U ≤ γ α` at every feasible point. -/
theorem Conform.costU_le {M ιx ιu : Type} [Fintype M] [Fintype ιx] [Fintype ιu] (nk ns : ℕ)
    (yb : M → ℕ → Vec ℝ q) (Cb : M → ℕ → Mat ℝ q n)
    (Db : M → (k : ℕ) → Fin (k + 1) → Mat ℝ q p) (dx : Vec ℝ n) (Gx : ιx → Vec ℝ n)
    (αx : ιx → ℝ) (du : Vec ℝ p) (Gu : ιu → Vec ℝ p) (αu : ιu → ℝ) (w : ℕ → ℝ)
    (hw : ∀ k, 0 ≤ w k) (y : M → Fin (ns + 1) → ℕ → Vec ℝ q)
    (hfeas : ∀ m, ∀ k < nk, ∀ s, ∃ β : ιx ⊕ (Fin (k + 1) × ιu) → ℝ,
      (∀ j, 0 ≤ Sum.elim αx (fun r : Fin (k + 1) × ιu => αu r.2) j + β j ∧
        0 ≤ Sum.elim αx (fun r : Fin (k + 1) × ιu => αu r.2) j - β j) ∧
      y m s k - yb m k = (Cb m k *ᵥ dx + ∑ i, Db m k i *ᵥ du)
        + ∑ j, β j • Sum.elim (fun j => Cb m k *ᵥ Gx j)
            (fun r : Fin (k + 1) × ιu => Db m k r.1 *ᵥ Gu r.2) j) : -- --- CONCL ---
    ∑ m, ∑ k ∈ Finset.range nk, w k * ∑ a, Finset.univ.sup' Finset.univ_nonempty
        (fun s => |(y m s k - yb m k - (Cb m k *ᵥ dx + ∑ i, Db m k i *ᵥ du)) a|)
      ≤ ∑ m, ∑ k ∈ Finset.range nk, w k * (∑ j, (∑ a, |(Cb m k *ᵥ Gx j) a|) * αx j
          + ∑ l, (∑ i : Fin (k + 1), ∑ a, |(Db m k i *ᵥ Gu l) a|) * αu l) := by -- --- PROOF ---
  refine Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun k hk => ?_
  refine mul_le_mul_of_nonneg_left ?_ (hw k)
  rw [Finset.mem_range] at hk
  -- per output coordinate, every execution is bounded by `|Q_β| R_α α`
  have hcoord : ∀ a, Finset.univ.sup' Finset.univ_nonempty
      (fun s => |(y m s k - yb m k - (Cb m k *ᵥ dx + ∑ i, Db m k i *ᵥ du)) a|)
      ≤ ∑ j, |Sum.elim (fun j => Cb m k *ᵥ Gx j)
          (fun r : Fin (k + 1) × ιu => Db m k r.1 *ᵥ Gu r.2) j a|
        * Sum.elim αx (fun r : Fin (k + 1) × ιu => αu r.2) j := by
    intro a
    refine Finset.sup'_le _ _ fun s _ => ?_
    obtain ⟨β, hβ, hy⟩ := hfeas m k hk s
    rw [hy, add_sub_cancel_left]
    exact aux_abs_comb_le _ β _ (fun j => abs_le.mpr ⟨by linarith [(hβ j).1],
      by linarith [(hβ j).2]⟩) a
  refine le_trans (Finset.sum_le_sum fun a _ => hcoord a) (le_of_eq ?_)
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin q)))]
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type,
    Finset.sum_mul]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin (k + 1))))]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
