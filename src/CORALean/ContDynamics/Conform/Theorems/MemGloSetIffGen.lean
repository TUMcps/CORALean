import CORALean.ContDynamics.Conform.Theorems.GloSetTemplateZono
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# [1, Lemma 4]: containment in `Ȳ` as generator constraints

`y ∈ Ȳ` iff some `β` has `0 ≤ R_α α + β`, `0 ≤ R_α α - β` (19a) and
`y - ȳ = Q_c c_Δ + Q_β β` (19b), for `α ≥ 0`: `β = diag(R_α α) λ` turns the zonotope's
`|λ| ≤ 1` into `|β| ≤ R_α α`, linear in `α` and `β` together. `R_α α = [α_x; α_u; …; α_u]`,
`Q_c c_Δ = C̄ c_Δ,x + ∑ᵢ D̄ᵢ c_Δ,u`, `Q_β` the template `[C̄ G_x, D̄₀ G_u, …, D̄ₖ G_u]`. Where a
factor `αⱼ` is `0`, `βⱼ = 0` is forced and the generator drops out, as from the zonotope.

## References

* [1] L. Lützow and M. Althoff. "Reachset-Conformant System Identification". IEEE
      Transactions on Automatic Control, 71(5):3014-3029, 2026.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n p q k : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Membership in a stretched template, with `βⱼ = αⱼ λⱼ` in place of `λⱼ`. -/
theorem aux_mem_templateZono_iff_gen {m : ℕ} {ι : Type} [Fintype ι] (c : Vec ℝ m)
    (G : ι → Vec ℝ m) (α : ι → ℝ) (hα : ∀ j, 0 ≤ α j) (y : Vec ℝ m) :
    y ∈ Conform.templateZono c G α ↔
      ∃ β : ι → ℝ, (∀ j, |β j| ≤ α j) ∧ y = c + ∑ j, β j • G j := by -- --- PROOF ---
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨fun j => l j * α j, fun j => ?_, by simp only [smul_smul]⟩
    rw [abs_mul, abs_of_nonneg (hα j)]
    exact mul_le_of_le_one_left (hα j) (hl j)
  · rintro ⟨β, hβ, rfl⟩
    -- `λⱼ = βⱼ / αⱼ`, and `0` where `αⱼ = 0` (then `βⱼ = 0` too)
    refine ⟨fun j => β j / α j, fun j => ?_, ?_⟩
    · rcases (hα j).lt_or_eq with hpos | hzero
      · rw [abs_div, abs_of_pos hpos, div_le_one hpos]
        exact hβ j
      · simp [← hzero]
    · congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul]
      congr 1
      show β j = β j / α j * α j
      rcases (hα j).lt_or_eq with hpos | hzero
      · field_simp
      · have : β j = 0 := abs_nonpos_iff.mp (hzero ▸ hβ j)
        simp [this, ← hzero]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 4]: `y ∈ Ȳ` iff (19a) and (19b) hold for some `β`. -/
theorem Conform.mem_gloSet_iff_gen {ιx ιu : Type} [Fintype ιx] [Fintype ιu] (yb : Vec ℝ q)
    (Cb : Mat ℝ q n) (Db : Fin (k + 1) → Mat ℝ q p) (cx dx : Vec ℝ n) (Gx : ιx → Vec ℝ n)
    (αx : ιx → ℝ) (cu du : Vec ℝ p) (Gu : ιu → Vec ℝ p) (αu : ιu → ℝ) (hαx : ∀ j, 0 ≤ αx j)
    (hαu : ∀ l, 0 ≤ αu l) (y : Vec ℝ q) :
    y ∈ Conform.gloSet yb Cb Db cx (Conform.templateZono (cx + dx) Gx αx) cu
        (fun _ => Conform.templateZono (cu + du) Gu αu) ↔
      ∃ β : ιx ⊕ (Fin (k + 1) × ιu) → ℝ,
        (∀ j, 0 ≤ Sum.elim αx (fun r : Fin (k + 1) × ιu => αu r.2) j + β j ∧
          0 ≤ Sum.elim αx (fun r : Fin (k + 1) × ιu => αu r.2) j - β j) ∧
        y - yb = (Cb *ᵥ dx + ∑ i, Db i *ᵥ du)
          + ∑ j, β j • Sum.elim (fun j => Cb *ᵥ Gx j)
              (fun r : Fin (k + 1) × ιu => Db r.1 *ᵥ Gu r.2) j := by -- --- PROOF ---
  rw [Conform.gloSet_templateZono, aux_mem_templateZono_iff_gen _ _ _
    fun j => by rcases j with x | r <;> simp [hαx, hαu]]
  refine exists_congr fun β => and_congr (forall_congr' fun j => ?_) ?_
  · rw [abs_le]
    constructor
    · rintro ⟨h₁, h₂⟩; exact ⟨by linarith, by linarith⟩
    · rintro ⟨h₁, h₂⟩; exact ⟨by linarith, by linarith⟩
  · constructor
    · intro h; rw [h]; abel
    · intro h; rw [← sub_add_cancel y yb, h]; abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
