import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.PolyZonotope.Real.Operations.LinComb
import CORALean.ContSet.Zonotope.Real.Theorems.LinCombOuter

/-!
# `linComb` contains every segment between the two polynomial zonotopes

The fresh factor takes `2λ - 1`, which is in `[-1,1]` exactly when `λ ∈ [0,1]`,
and the two sets keep their own factors unchanged: the dependent part of the
segment is reproduced, not enclosed.

The independent block is where something is given away. Its coefficients come
out as `pairCoeffSum` and `pairCoeffDiff`, the zonotope pairing's, which do
record that the two sides share one `λ`; what they cannot record is that the
same `λ` also drives the dependent part. So the containment is one-way and the
statement is `_outer` rather than `_exact`.

Nothing here asks for convexity, as nothing in `segments` does; a polynomial
zonotope is generally not convex and this claim is still the right one.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   03-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

/-- `Fin.sum_univ_add` at `linComb`'s dependent generator count, stated through
the projection because that is the form the goal has. Only the outermost split
needs it; the blocks it produces have plain counts simp can split itself. -/
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

theorem PolyZonotope.linComb_outer (PZ₁ PZ₂ : PolyZonotope α) :
    segments PZ₁.construct PZ₂.construct ⊆ (PZ₁.linComb PZ₂).construct := by
  rintro x ⟨y₁, ⟨a₁, β₁, ha₁, hβ₁, rfl⟩, y₂, ⟨a₂, β₂, ha₂, hβ₂, rfl⟩,
    lam, ⟨hl0, hl1⟩, rfl⟩
  refine ⟨Fin.append (Fin.append a₁ a₂) (fun _ : Fin 1 => 2 * lam - 1),
    Fin.append (Zonotope.pairCoeffSum β₁ β₂ lam) (Zonotope.pairCoeffDiff β₁ β₂ lam),
    ?_, ?_, ?_⟩
  -- the fresh factor is `2λ-1`, which stays in `[-1,1]` for `λ` in the unit interval
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
      simpa using Zonotope.abs_pairCoeffSum_le_one hβ₁ hβ₂ hl0 hl1 j
    · intro j
      simpa using Zonotope.abs_pairCoeffDiff_le_one hβ₁ hβ₂ hl0 hl1 j
  -- the value: the three dependent blocks and the paired independent one recombine
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
      Zonotope.sum_pair PZ₁.GI PZ₂.GI β₁ β₂ lam]
    module

end CORALean.Real
