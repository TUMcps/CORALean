module

public import CORALean.ContDynamics.LinearSysDT.Definitions.IsHMinusStepPositive
public import CORALean.ContDynamics.LinearSysDT.Definitions.IsHMinusLmiPhi

@[expose] public section

/-!
# The `H₋` step condition is the matrix inequality in `(e, f)`

[1, Eq. 24], [1, Eq. 25]: for a symmetric `Q`, the quantity `pᵀp - β²fᵀf - (V⁺ - V)` of Eq. 24
(`LinearSysDT.IsHMinusStepPositive`) is positive at every `(e, f) ≠ 0` iff `[Φ₁₁ Φ₁₂; ⋆ Φ₂₂] ≺ 0`
(`LinearSysDT.IsHMinusLmiPhi`). The form of `-Φ` at `(e, f)` is that quantity: `pᵀp` expands to
`eᵀCᵀMᵀMCe + 2eᵀCᵀMᵀMEf + fᵀEᵀMᵀMEf`, `e⁺ᵀQe⁺` to the blocks `(A - LC)ᵀQ(A - LC)`,
`(A - LC)ᵀQ(-LE)` and `(LE)ᵀQ(LE)`, as `Q` is symmetric.

## Inputs
* `A` – state matrix
* `C` – output matrix
* `E` – fault matrix
* `L` – observer gain
* `Q` – Lyapunov matrix
* `M` – residual weight
* `β` – sensitivity level

## Hypotheses
* `hQ` – Lyapunov matrix symmetric

## Conclusion
* positivity of the step quantity is equivalent to the block inequality

## References

* [1] Y. Wang, M. Zhou, V. Puig, G. Cembrano and Z. Wang. "Zonotopic Fault Detection Observer
      with H− Performance". In Proc. of the 36th Chinese Control Conference (CCC),
      pp. 7230-7235, 2017.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n ny nf : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- the form of `-Φ` at `(e, f)` is the quantity of Eq. 24
theorem LinearSysDT.aux_hMinusPhi_form (A : Mat ℝ n n) (C : Mat ℝ ny n) (E : Mat ℝ ny nf)
    (L : Mat ℝ n ny) (Q : Mat ℝ n n) (M : Mat ℝ ny ny) (β : ℝ) (hQ : Qᵀ = Q) (e : Vec ℝ n)
    (f : Vec ℝ nf) : -- --- CONCL ---
    let Φ₁₁ : Mat ℝ n n := -(Cᵀ * Mᵀ * M * C) + (A - L * C)ᵀ * Q * (A - L * C) - Q
    let Φ₁₂ : Matrix (Fin n) (Fin nf) ℝ := (A - L * C)ᵀ * Q * (-(L * E)) - Cᵀ * Mᵀ * M * E
    let Φ₂₂ : Mat ℝ nf nf := β ^ 2 • 1 - Eᵀ * Mᵀ * M * E + (L * E)ᵀ * Q * (L * E)
    let w := (A - L * C) *ᵥ e - (L * E) *ᵥ f
    let p := (M * C) *ᵥ e + (M * E) *ᵥ f
    (Sum.elim e f : Fin n ⊕ Fin nf → ℝ) ⬝ᵥ
        ((-(fromBlocks Φ₁₁ Φ₁₂ Φ₁₂ᵀ Φ₂₂)) *ᵥ Sum.elim e f) =
      p ⬝ᵥ p - β ^ 2 * (f ⬝ᵥ f) - (w ⬝ᵥ (Q *ᵥ w) - e ⬝ᵥ (Q *ᵥ e)) := by -- --- PROOF ---
  intro Φ₁₁ Φ₁₂ Φ₂₂ w p
  -- `Xᵀ MᵀM Z` as a dot product of `M X` and `M Z`
  have hY : ∀ {k l : ℕ} (X : Mat ℝ ny k) (Z : Mat ℝ ny l) (a : Vec ℝ k) (b : Vec ℝ l),
      a ⬝ᵥ ((Xᵀ * Mᵀ * M * Z) *ᵥ b) = ((M * X) *ᵥ a) ⬝ᵥ ((M * Z) *ᵥ b) := by
    intro k l X Z a b
    have h : Xᵀ * Mᵀ * M * Z = (M * X)ᵀ * (M * Z) := by
      rw [transpose_mul]; simp only [Matrix.mul_assoc]
    rw [h, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  -- `Xᵀ Q Z` as a dot product of `X` and `Q Z`
  have hQf : ∀ {k l : ℕ} (X : Mat ℝ n k) (Z : Mat ℝ n l) (a : Vec ℝ k) (b : Vec ℝ l),
      a ⬝ᵥ ((Xᵀ * Q * Z) *ᵥ b) = (X *ᵥ a) ⬝ᵥ (Q *ᵥ (Z *ᵥ b)) := by
    intro k l X Z a b
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  have hT : f ⬝ᵥ (Φ₁₂ᵀ *ᵥ e) = e ⬝ᵥ (Φ₁₂ *ᵥ f) := by
    rw [mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]
  have hsym : ∀ u v : Vec ℝ n, u ⬝ᵥ (Q *ᵥ v) = v ⬝ᵥ (Q *ᵥ u) := by
    intro u v
    rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hQ]
  -- the six pieces of the form
  have h1 : e ⬝ᵥ ((Cᵀ * Mᵀ * M * C) *ᵥ e) = ((M * C) *ᵥ e) ⬝ᵥ ((M * C) *ᵥ e) := hY C C e e
  have h2 : e ⬝ᵥ (((A - L * C)ᵀ * Q * (A - L * C)) *ᵥ e) =
      ((A - L * C) *ᵥ e) ⬝ᵥ (Q *ᵥ ((A - L * C) *ᵥ e)) := hQf _ _ e e
  have h3 : e ⬝ᵥ (((A - L * C)ᵀ * Q * (-(L * E))) *ᵥ f) =
      -(((A - L * C) *ᵥ e) ⬝ᵥ (Q *ᵥ ((L * E) *ᵥ f))) := by
    rw [hQf, neg_mulVec, mulVec_neg, dotProduct_neg]
  have h4 : e ⬝ᵥ ((Cᵀ * Mᵀ * M * E) *ᵥ f) = ((M * C) *ᵥ e) ⬝ᵥ ((M * E) *ᵥ f) := hY C E e f
  have h5 : f ⬝ᵥ ((Eᵀ * Mᵀ * M * E) *ᵥ f) = ((M * E) *ᵥ f) ⬝ᵥ ((M * E) *ᵥ f) := hY E E f f
  have h6 : f ⬝ᵥ (((L * E)ᵀ * Q * (L * E)) *ᵥ f) =
      ((L * E) *ᵥ f) ⬝ᵥ (Q *ᵥ ((L * E) *ᵥ f)) := hQf _ _ f f
  simp only [fromBlocks_neg, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    sumElim_dotProduct_sumElim, dotProduct_add, neg_mulVec, dotProduct_neg, hT]
  simp only [Φ₁₁, Φ₁₂, Φ₂₂, w, p, sub_mulVec, add_mulVec, neg_mulVec, dotProduct_sub,
    dotProduct_add, dotProduct_neg, smul_mulVec, dotProduct_smul, one_mulVec, smul_eq_mul, h1, h2,
    h3, h4, h5, h6, mulVec_sub, dotProduct_sub, sub_dotProduct, add_dotProduct, dotProduct_add]
  rw [hsym ((L * E) *ᵥ f) (A *ᵥ e), hsym ((L * E) *ᵥ f) ((L * C) *ᵥ e),
    dotProduct_comm ((M * E) *ᵥ f) ((M * C) *ᵥ e)]
  ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.hMinusStepPositive_iff_phi (A : Mat ℝ n n) (C : Mat ℝ ny n)
    (E : Mat ℝ ny nf) (L : Mat ℝ n ny) (Q : Mat ℝ n n) (M : Mat ℝ ny ny) (β : ℝ)
    (hQ : Qᵀ = Q) : -- --- CONCL ---
    LinearSysDT.IsHMinusStepPositive A C E L Q M β ↔
      LinearSysDT.IsHMinusLmiPhi A C E L Q M β := by -- --- PROOF ---
  unfold LinearSysDT.IsHMinusStepPositive LinearSysDT.IsHMinusLmiPhi
  simp only
  set Φ₁₁ : Mat ℝ n n := -(Cᵀ * Mᵀ * M * C) + (A - L * C)ᵀ * Q * (A - L * C) - Q with hΦ₁₁
  set Φ₁₂ : Matrix (Fin n) (Fin nf) ℝ := (A - L * C)ᵀ * Q * (-(L * E)) - Cᵀ * Mᵀ * M * E
    with hΦ₁₂
  set Φ₂₂ : Mat ℝ nf nf := β ^ 2 • 1 - Eᵀ * Mᵀ * M * E + (L * E)ᵀ * Q * (L * E) with hΦ₂₂
  -- the block matrix is symmetric, as `Q` is
  have hherm : (-(fromBlocks Φ₁₁ Φ₁₂ Φ₁₂ᵀ Φ₂₂)).IsHermitian := by
    have h11 : Φ₁₁ᵀ = Φ₁₁ := by
      simp only [hΦ₁₁, transpose_add, transpose_sub, transpose_neg, transpose_mul,
        transpose_transpose, hQ, Matrix.mul_assoc]
    have h22 : Φ₂₂ᵀ = Φ₂₂ := by
      simp only [hΦ₂₂, transpose_add, transpose_sub, transpose_smul, transpose_one, transpose_mul,
        transpose_transpose, hQ, Matrix.mul_assoc]
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_neg, fromBlocks_transpose,
      transpose_transpose, h11, h22]
  rw [posDef_iff_dotProduct_mulVec]
  simp only [star_trivial]
  refine ⟨fun h => ⟨hherm, fun v hv => ?_⟩, fun h e f hef => ?_⟩
  · -- split `v = (e, f)` and read the form off the identity
    obtain ⟨e, f, rfl⟩ : ∃ e f, v = Sum.elim e f :=
      ⟨v ∘ Sum.inl, v ∘ Sum.inr, (Sum.elim_comp_inl_inr v).symm⟩
    rw [LinearSysDT.aux_hMinusPhi_form A C E L Q M β hQ e f]
    exact h e f hv
  · have := h.2 hef
    rwa [LinearSysDT.aux_hMinusPhi_form A C E L Q M β hQ e f] at this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
