import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.PolyZonotope.Real.Operations.LinComb

/-!
# `linComb` contains every segment between the two polynomial zonotopes

The fresh factor takes `2λ - 1`, which is in `[-1,1]` exactly when `λ ∈ [0,1]`,
and the two sets keep their own factors unchanged: the dependent part of the
segment is reproduced, not enclosed.

The independent coefficients are where something is given away. They come out as
`λβ₁` and `(1-λ)β₂`, both back in `[-1,1]`, but the representation cannot record
that they are tied to the same `λ` as the dependent part — so the containment is
one-way and the statement is `_outer` rather than `_exact`.

Nothing here asks for convexity, as nothing in `segments` does; a polynomial
zonotope is generally not convex and this claim is still the right one.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

/-- `Fin.sum_univ_add` at `linComb`'s dependent generator count, stated through
the projection because that is the form the goal has and simp will not rewrite a
binder's type. Only the outermost split needs it; the blocks it produces have
plain counts that simp can split for itself. -/
theorem PolyZonotope.aux_sum_univ_linComb_h {PZ₁ PZ₂ : PolyZonotope α}
    (f : Fin (PZ₁.h + PZ₂.h + (PZ₁.h + PZ₂.h + 1)) → α) :
    ∑ i : Fin (PZ₁.linComb PZ₂).h, f i
      = ∑ i, f (Fin.castAdd (PZ₁.h + PZ₂.h + 1) i)
        + ∑ i, f (Fin.natAdd (PZ₁.h + PZ₂.h) i) :=
  Fin.sum_univ_add f

/-- The same at the independent generator count. -/
theorem PolyZonotope.aux_sum_univ_linComb_q {PZ₁ PZ₂ : PolyZonotope α}
    (f : Fin (PZ₁.q + PZ₂.q) → α) :
    ∑ j : Fin (PZ₁.linComb PZ₂).q, f j
      = ∑ j, f (Fin.castAdd PZ₂.q j) + ∑ j, f (Fin.natAdd PZ₁.q j) :=
  Fin.sum_univ_add f

/-- Scaling a coefficient by a weight in `[0,1]` keeps it a coefficient. -/
theorem PolyZonotope.aux_abs_mul_le_one {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb : |b| ≤ 1) : |a * b| ≤ 1 := by
  rw [abs_mul, abs_of_nonneg ha0]
  nlinarith [abs_nonneg b]

/-- A generator block scaled by a constant, with the constant pulled out of the
sum: `module` cannot do this for itself, a sum being one atom to it. -/
theorem PolyZonotope.aux_sum_scaled {k : ℕ} (s : ℝ) (m : Fin k → ℝ) (G : Fin k → α) :
    ∑ i, m i • (s • G i) = s • ∑ i, m i • G i := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, smul_smul, mul_comm]

/-- The same where the coefficients also carry a common factor, which is the
shape the second dependent block has. -/
theorem PolyZonotope.aux_sum_scaled_mul {k : ℕ} (t s : ℝ) (m : Fin k → ℝ) (G : Fin k → α) :
    ∑ i, (t * m i) • (s • G i) = (t * s) • ∑ i, m i • G i := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, smul_smul]
  congr 1
  ring

/-- The same at a block whose generators are not scaled, which is what the
independent block is. -/
theorem PolyZonotope.aux_sum_mul {k : ℕ} (t : ℝ) (b : Fin k → ℝ) (G : Fin k → α) :
    ∑ j, (t * b j) • G j = t • ∑ j, b j • G j := by
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => (smul_smul t (b j) (G j)).symm

theorem PolyZonotope.linComb_outer (PZ₁ PZ₂ : PolyZonotope α) :
    segments PZ₁.construct PZ₂.construct ⊆ (PZ₁.linComb PZ₂).construct := by
  rintro x ⟨y₁, ⟨a₁, β₁, ha₁, hβ₁, rfl⟩, y₂, ⟨a₂, β₂, ha₂, hβ₂, rfl⟩,
    lam, ⟨hl0, hl1⟩, rfl⟩
  refine ⟨Fin.append (Fin.append a₁ a₂) (fun _ : Fin 1 => 2 * lam - 1),
    Fin.append (fun j => lam * β₁ j) (fun j => (1 - lam) * β₂ j), ?_, ?_, ?_⟩
  · refine Fin.addCases ?_ ?_
    · refine Fin.addCases ?_ ?_
      · intro k
        simpa using ha₁ k
      · intro k
        simpa using ha₂ k
    · intro _
      simp only [Fin.append_right]
      rw [abs_le]
      constructor <;> linarith
  · refine Fin.addCases ?_ ?_
    · intro j
      simpa using PolyZonotope.aux_abs_mul_le_one hl0 hl1 (hβ₁ j)
    · intro j
      simpa using PolyZonotope.aux_abs_mul_le_one (by linarith) (by linarith) (hβ₂ j)
  · rw [PolyZonotope.aux_sum_univ_linComb_h, PolyZonotope.aux_sum_univ_linComb_q]
    simp only [PolyZonotope.linComb, Fin.sum_univ_add, Fin.sum_univ_one,
      PolyZonotope.monomial_linCombE_fst, PolyZonotope.monomial_linCombE_snd,
      PolyZonotope.monomial_linCombE_last, PolyZonotope.monomial_plusE_left,
      PolyZonotope.monomial_plusE_right, Fin.append_left, Fin.append_right]
    rw [PolyZonotope.aux_sum_scaled (2:ℝ)⁻¹ (PolyZonotope.monomial PZ₁.E a₁) PZ₁.G,
      PolyZonotope.aux_sum_scaled (2:ℝ)⁻¹ (PolyZonotope.monomial PZ₂.E a₂) PZ₂.G,
      PolyZonotope.aux_sum_scaled_mul (2 * lam - 1) (2:ℝ)⁻¹
        (PolyZonotope.monomial PZ₁.E a₁) PZ₁.G,
      PolyZonotope.aux_sum_scaled_mul (2 * lam - 1) (-(2:ℝ)⁻¹)
        (PolyZonotope.monomial PZ₂.E a₂) PZ₂.G,
      PolyZonotope.aux_sum_mul lam β₁ PZ₁.GI,
      PolyZonotope.aux_sum_mul (1 - lam) β₂ PZ₂.GI]
    module

end CORALean.Real
