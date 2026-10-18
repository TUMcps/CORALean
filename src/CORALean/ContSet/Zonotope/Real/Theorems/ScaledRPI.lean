module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# A diagonally-scaled zonotope, robust positively invariant

`[1, Thm. 6]`: for the system `x⁺ = A x ⊕ w`, `w ∈ W = {Gw, cw}`, a sufficient condition for the
zonotope `Z = {GΦ, c}`, `Φ = diag(φ)`, `φᵢ > 0`, to be a robust positively invariant (RPI) set —
`A '' Z ⊕ W ⊆ Z`, `[1, Def. 3]`, restated directly here since the definition itself is not carried
elsewhere in this tree — is the existence of `Γ1`, `Γ2`, `β` with

* `φⱼ • A Gⱼ = ∑ᵢ Γ1ᵢⱼ • Gᵢ`     (`eq. (28a)`, `AGΦ = GΓ1` read one column at a time)
* `Gwₖ = ∑ᵢ Γ2ᵢₖ • Gᵢ`           (`eq. (28b)`, `Gw = GΓ2`)
* `c - A c - cw = ∑ᵢ βᵢ • Gᵢ`     (`eq. (28c)`, `(I - A) c - cw = Gβ`)
* `∑ⱼ |Γ1ᵢⱼ| + ∑ₖ |Γ2ᵢₖ| + |βᵢ| ≤ φᵢ`, every row `i`  (`eq. (28d)`)

The paper's own proof reduces this to the Sadraddini–Tedrake containment condition (`Lemma 3`,
not drawn on here — see the page); this file gives the direct argument that condition would give
at `Γ := [Γ1 Γ2]`, `β := β`, after the change of variables the paper's proof makes: since `φᵢ > 0`,
a coefficient `βᵢ` for `Z` need only satisfy `|βᵢ φᵢ| ≤ φᵢ`, i.e. `|βᵢ| ≤ 1`.

## References

* [1] V. Raghuraman and J. P. Koeln. "Set operations and order reductions for
      constrained zonotopes". Automatica, 139:110204, 2022. arXiv:2009.06039.
-/

-- Authors:       Claude Opus 5
-- Written:       21-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A generator family reached through `Γ`, at any admissible coefficients, regroups into `G`'s
own — the double-sum swap `eq. (28a)`'s and `(28b)`'s substitutions both need. -/
theorem Zonotope.aux_regroup_scaled_rpi {ng m : ℕ} (G : Fin ng → α) (Γ : Fin ng → Fin m → ℝ)
    (H : Fin m → α) (hΓ : ∀ k, H k = ∑ i, Γ i k • G i) (w : Fin m → ℝ) :
    ∑ k, w k • H k = ∑ i, (∑ k, Γ i k * w k) • G i := by
  simp_rw [hΓ, Finset.smul_sum, smul_smul, mul_comm (w _)]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 6]: `Z = {GΦ, c}` is an RPI set of `x⁺ = A x ⊕ w`, `w ∈ W`, given `Γ1`, `Γ2`, `β`
meeting `eq. (28)`. -/
theorem Zonotope.scaled_rpi {ng : ℕ} (G : Fin ng → α) (c : α) (φ : Fin ng → ℝ)
    (hφ : ∀ i, 0 < φ i) (A : α →ₗ[ℝ] α) (W : Zonotope α) (Γ1 : Fin ng → Fin ng → ℝ)
    (Γ2 : Fin ng → Fin W.h → ℝ) (β : Fin ng → ℝ)
    (hA : ∀ j, φ j • A (G j) = ∑ i, Γ1 i j • G i) (hW : ∀ k, W.G k = ∑ i, Γ2 i k • G i)
    (hc : c - A c - W.c = ∑ i, β i • G i)
    (hbound : ∀ i, (∑ j, |Γ1 i j|) + (∑ k, |Γ2 i k|) + |β i| ≤ φ i) : -- --- STMT ---
    (A · : α → α) '' (⟨ng, c, fun j => φ j • G j⟩ : Zonotope α).construct + W.construct
      ⊆ (⟨ng, c, fun j => φ j • G j⟩ : Zonotope α).construct := by -- --- PROOF ---
  rintro y ⟨_, ⟨x, ⟨ψ, hψ, rfl⟩, rfl⟩, w, ⟨μ, hμ, rfl⟩, rfl⟩
  dsimp only
  -- `A`'s image of `x`: `φⱼ • A Gⱼ`'s own regrouping via `Γ1`, at `hA`
  have hAx : A (c + ∑ j, ψ j • φ j • G j) = A c + ∑ i, (∑ j, Γ1 i j * ψ j) • G i := by
    rw [map_add, map_sum]
    congr 1
    simp_rw [map_smul]
    exact Zonotope.aux_regroup_scaled_rpi G Γ1 (fun j => φ j • A (G j)) hA ψ
  -- `w`'s own regrouping via `Γ2`, at `hW`
  have hw : W.c + ∑ k, μ k • W.G k = W.c + ∑ i, (∑ k, Γ2 i k * μ k) • G i := by
    congr 1
    exact Zonotope.aux_regroup_scaled_rpi G Γ2 W.G hW μ
  -- the fresh coefficient, and its bound from `hbound` and `|ψ|, |μ| ≤ 1`
  set γ : Fin ng → ℝ := fun i => (∑ j, Γ1 i j * ψ j) + (∑ k, Γ2 i k * μ k) - β i with hγdef
  have hγb : ∀ i, |γ i| ≤ φ i := by
    intro i
    have h1 : |∑ j, Γ1 i j * ψ j| ≤ ∑ j, |Γ1 i j| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (by
        refine Finset.sum_le_sum fun j _ => ?_
        calc |Γ1 i j * ψ j| = |Γ1 i j| * |ψ j| := abs_mul _ _
          _ ≤ |Γ1 i j| * 1 := mul_le_mul_of_nonneg_left (hψ j) (abs_nonneg _)
          _ = |Γ1 i j| := mul_one _)
    have h2 : |∑ k, Γ2 i k * μ k| ≤ ∑ k, |Γ2 i k| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (by
        refine Finset.sum_le_sum fun k _ => ?_
        calc |Γ2 i k * μ k| = |Γ2 i k| * |μ k| := abs_mul _ _
          _ ≤ |Γ2 i k| * 1 := mul_le_mul_of_nonneg_left (hμ k) (abs_nonneg _)
          _ = |Γ2 i k| := mul_one _)
    -- the three pieces of `γ i`, triangle-inequalitied back together
    have h3 : |(∑ j, Γ1 i j * ψ j) + (∑ k, Γ2 i k * μ k) - β i|
        ≤ |(∑ j, Γ1 i j * ψ j) + (∑ k, Γ2 i k * μ k)| + |β i| := by
      rw [sub_eq_add_neg]
      calc |(∑ j, Γ1 i j * ψ j) + (∑ k, Γ2 i k * μ k) + -β i|
          ≤ |(∑ j, Γ1 i j * ψ j) + (∑ k, Γ2 i k * μ k)| + |-β i| := abs_add_le _ _
        _ = |(∑ j, Γ1 i j * ψ j) + (∑ k, Γ2 i k * μ k)| + |β i| := by rw [abs_neg]
    have h4 : |(∑ j, Γ1 i j * ψ j) + (∑ k, Γ2 i k * μ k)|
        ≤ |∑ j, Γ1 i j * ψ j| + |∑ k, Γ2 i k * μ k| := abs_add_le _ _
    simp only [hγdef]
    linarith [h1, h2, h3, h4, hbound i]
  refine ⟨fun i => γ i / φ i, fun i => ?_, ?_⟩
  · rw [abs_div, abs_of_pos (hφ i), div_le_one (hφ i)]; exact hγb i
  · rw [hAx, hw]
    -- `(28c)` moved across, then the three generator sums combined term by term
    have hac : A c + W.c = c - ∑ i, β i • G i := by
      rw [eq_sub_iff_add_eq, ← hc]; abel
    rw [add_add_add_comm, hac]
    have hcomb : c - ∑ i, β i • G i
        + ((∑ i, (∑ j, Γ1 i j * ψ j) • G i) + ∑ i, (∑ k, Γ2 i k * μ k) • G i)
        = c + ∑ i, γ i • G i := by
      simp only [hγdef, sub_smul, add_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      abel
    rw [hcomb]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, div_mul_cancel₀ _ (hφ i).ne']

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
