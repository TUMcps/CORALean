module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.Zonotope.Real.Zonotope

@[expose] public section

/-!
# A diagonally-scaled zonotope, an inner-approximation of the Pontryagin difference

`[1, Thm. 7]`: given zonotopes `Z1 = {G1, c1}`, `Z2 = {G2, c2}`, a sufficient condition for
`Z̃d = {[G1 G2]Φ, cd}`, `Φ = diag(φ)`, `φₖ > 0`, to be an inner-approximation
`Z̃d ⊆ Z1 ⊖ Z2` of the Pontryagin difference — `minkowskiDiff`, `[1, Def. 5]` — is the existence of
`Γ`, `β` with

* `φₖ • [G1 G2]ₖ = ∑ⱼ Γₐⱼₖ • G1ⱼ`, every generator `k` of `[G1 G2]`        (`eq. (32a)`, left)
* `G2ᵢ = ∑ⱼ Γᵦⱼᵢ • G1ⱼ`, every generator `i` of `G2`                     (`eq. (32a)`, right)
* `c1 - (cd + c2) = ∑ⱼ βⱼ • G1ⱼ`                                          (`eq. (32b)`)
* `∑ₖ |Γₐⱼₖ| + ∑ᵢ |Γᵦⱼᵢ| + |βⱼ| ≤ 1`, every row `j`                       (`eq. (32c)`)

`Γₐ`, `Γᵦ` are `[1]`'s single `Γ ∈ ℝ^{ng1×(ng1+2ng2)}` split into the two column blocks `(32a)`
concatenates, not a different hypothesis. The paper's own proof reduces this to the
Sadraddini–Tedrake containment condition (`Lemma 3`, not drawn on here — see the page) for
`Z̃d ⊕ Z2 ⊆ Z1`; this file gives the direct argument that condition would give at `Γ := [Γₐ Γᵦ]`.

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

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A generator family reached through `Γ`, at any admissible coefficients, regroups into `G`'s
own — the double-sum swap both `(32a)`'s blocks need. -/
theorem Zonotope.aux_regroup_minkDiffScaled {ng m : ℕ} (G : Fin ng → α) (Γ : Fin ng → Fin m → ℝ)
    (H : Fin m → α) (hΓ : ∀ k, H k = ∑ j, Γ j k • G j) (w : Fin m → ℝ) :
    ∑ k, w k • H k = ∑ j, (∑ k, Γ j k * w k) • G j := by
  simp_rw [hΓ, Finset.smul_sum, smul_smul, mul_comm (w _)]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 7]: `Z̃d = {[G1 G2]Φ, cd}` is an inner-approximation of `Z1 ⊖ Z2`, given `Γₐ`, `Γᵦ`,
`β` meeting `eq. (32)`. -/
theorem Zonotope.minkDiffScaled_inner (Z1 Z2 : Zonotope α) (φ : Fin (Z1.h + Z2.h) → ℝ)
    (_hφ : ∀ k, 0 < φ k) (cd : α) (ΓA : Fin Z1.h → Fin (Z1.h + Z2.h) → ℝ)
    (ΓB : Fin Z1.h → Fin Z2.h → ℝ) (β : Fin Z1.h → ℝ)
    (hA : ∀ k, φ k • Fin.append Z1.G Z2.G k = ∑ j, ΓA j k • Z1.G j)
    (hB : ∀ i, Z2.G i = ∑ j, ΓB j i • Z1.G j)
    (hc : Z1.c - (cd + Z2.c) = ∑ j, β j • Z1.G j)
    (hbound : ∀ j, (∑ k, |ΓA j k|) + (∑ i, |ΓB j i|) + |β j| ≤ 1) : -- --- STMT ---
    (⟨Z1.h + Z2.h, cd, fun k => φ k • Fin.append Z1.G Z2.G k⟩ : Zonotope α).construct
      ⊆ minkowskiDiff Z1.construct Z2.construct := by -- --- PROOF ---
  rintro x ⟨ψ, hψ, rfl⟩ y ⟨μ, hμ, rfl⟩
  -- the two blocks of `x`'s own sum, each regrouped into `Z1`'s generators via `hA`, `hB`
  have hx : cd + ∑ k, ψ k • φ k • Fin.append Z1.G Z2.G k
      = cd + ∑ j, (∑ k, ΓA j k * ψ k) • Z1.G j := by
    congr 1
    exact Zonotope.aux_regroup_minkDiffScaled Z1.G ΓA (fun k => φ k • Fin.append Z1.G Z2.G k)
      hA ψ
  have hy : Z2.c + ∑ i, μ i • Z2.G i = Z2.c + ∑ j, (∑ i, ΓB j i * μ i) • Z1.G j := by
    congr 1
    exact Zonotope.aux_regroup_minkDiffScaled Z1.G ΓB Z2.G hB μ
  -- the fresh coefficient, and its bound from `hbound` and `|ψ|, |μ| ≤ 1`
  set γ : Fin Z1.h → ℝ := fun j => (∑ k, ΓA j k * ψ k) + (∑ i, ΓB j i * μ i) - β j with hγdef
  have hγb : ∀ j, |γ j| ≤ 1 := by
    intro j
    have h1 : |∑ k, ΓA j k * ψ k| ≤ ∑ k, |ΓA j k| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (by
        refine Finset.sum_le_sum fun k _ => ?_
        calc |ΓA j k * ψ k| = |ΓA j k| * |ψ k| := abs_mul _ _
          _ ≤ |ΓA j k| * 1 := mul_le_mul_of_nonneg_left (hψ k) (abs_nonneg _)
          _ = |ΓA j k| := mul_one _)
    have h2 : |∑ i, ΓB j i * μ i| ≤ ∑ i, |ΓB j i| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (by
        refine Finset.sum_le_sum fun i _ => ?_
        calc |ΓB j i * μ i| = |ΓB j i| * |μ i| := abs_mul _ _
          _ ≤ |ΓB j i| * 1 := mul_le_mul_of_nonneg_left (hμ i) (abs_nonneg _)
          _ = |ΓB j i| := mul_one _)
    -- the three pieces of `γ j`, triangle-inequalitied back together
    have h3 : |(∑ k, ΓA j k * ψ k) + (∑ i, ΓB j i * μ i) - β j|
        ≤ |(∑ k, ΓA j k * ψ k) + (∑ i, ΓB j i * μ i)| + |β j| := by
      rw [sub_eq_add_neg]
      calc |(∑ k, ΓA j k * ψ k) + (∑ i, ΓB j i * μ i) + -β j|
          ≤ |(∑ k, ΓA j k * ψ k) + (∑ i, ΓB j i * μ i)| + |-β j| := abs_add_le _ _
        _ = |(∑ k, ΓA j k * ψ k) + (∑ i, ΓB j i * μ i)| + |β j| := by rw [abs_neg]
    have h4 : |(∑ k, ΓA j k * ψ k) + (∑ i, ΓB j i * μ i)|
        ≤ |∑ k, ΓA j k * ψ k| + |∑ i, ΓB j i * μ i| := abs_add_le _ _
    simp only [hγdef]
    linarith [h1, h2, h3, h4, hbound j]
  refine ⟨γ, hγb, ?_⟩
  show cd + ∑ k, ψ k • φ k • Fin.append Z1.G Z2.G k + (Z2.c + ∑ i, μ i • Z2.G i)
      = Z1.c + ∑ j, γ j • Z1.G j
  rw [hx, hy]
  -- `(32b)` moved across, then the two generator sums combined term by term
  have hc' : cd + Z2.c = Z1.c - ∑ j, β j • Z1.G j := by
    rw [eq_sub_iff_add_eq, ← hc]; abel
  have hcomb : cd + ∑ j, (∑ k, ΓA j k * ψ k) • Z1.G j
      + (Z2.c + ∑ j, (∑ i, ΓB j i * μ i) • Z1.G j)
      = Z1.c + ∑ j, γ j • Z1.G j := by
    rw [add_add_add_comm, hc']
    simp only [hγdef, sub_smul, add_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    abel
  exact hcomb

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
