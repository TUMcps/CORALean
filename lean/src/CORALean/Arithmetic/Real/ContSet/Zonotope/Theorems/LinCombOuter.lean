import CORALean.Arithmetic.Real.ContSet.Zonotope.Operations.LinComb

/-!
# `linComb` contains every segment between the two zonotopes

The coefficients are `λ β₁` and `(1-λ) β₂` on the two generator blocks, both
back in `[-1,1]` because `λ ∈ [0,1]`, and `2λ - 1` on the generator spanning the
half-difference of the centres.

Nothing here asks for convexity: the claim is about the segments themselves, so
it is the statement a non-convex representation could also make.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Real

variable {n : ℕ}

/-- Scaling a coefficient by a weight in `[0,1]` keeps it a coefficient. -/
theorem aux_abs_mul_le_one {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb : |b| ≤ 1) :
    |a * b| ≤ 1 := by
  rw [abs_mul, abs_of_nonneg ha0]
  nlinarith [abs_nonneg b]

/-- `Fin.sum_univ_add` at this operation's generator count, stated through the
projection because that is the form the goal has and simp will not rewrite a
binder's type. -/
theorem Zonotope.aux_sum_univ_linComb {Z₁ Z₂ : Zonotope n}
    (f : Fin (Z₁.h + Z₂.h + 1) → ℝ) :
    ∑ j : Fin (Z₁.linComb Z₂).h, f j
      = ∑ j, f (Fin.castAdd 1 j) + ∑ j, f (Fin.natAdd (Z₁.h + Z₂.h) j) :=
  Fin.sum_univ_add f

set_option maxHeartbeats 400000 in
theorem Zonotope.linComb_outer (Z₁ Z₂ : Zonotope n) :
    segments Z₁.construct Z₂.construct ⊆ (Z₁.linComb Z₂).construct := by
  rintro x ⟨y₁, ⟨β₁, hβ₁, hy₁⟩, y₂, ⟨β₂, hβ₂, hy₂⟩, lam, ⟨hl0, hl1⟩, rfl⟩
  refine ⟨Fin.append (Fin.append (fun j => lam * β₁ j) (fun j => (1 - lam) * β₂ j))
      (fun _ : Fin 1 => 2 * lam - 1), ?_, fun i => ?_⟩
  · refine Fin.addCases ?_ ?_
    · refine Fin.addCases ?_ ?_
      · intro j
        simpa using aux_abs_mul_le_one hl0 hl1 (hβ₁ j)
      · intro j
        simpa using aux_abs_mul_le_one (by linarith) (by linarith) (hβ₂ j)
    · intro _
      simp only [Fin.append_right]
      rw [abs_le]
      constructor <;> linarith
  · show lam * y₁ i + (1 - lam) * y₂ i = _
    rw [hy₁ i, hy₂ i, Zonotope.aux_sum_univ_linComb]
    simp only [Zonotope.linComb, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
      Fin.sum_univ_one]
    rw [Finset.sum_congr rfl (fun j _ => by ring : ∀ j ∈ Finset.univ,
        Z₁.G i j * (lam * β₁ j) = lam * (Z₁.G i j * β₁ j)),
      Finset.sum_congr rfl (fun j _ => by ring : ∀ j ∈ Finset.univ,
        Z₂.G i j * ((1 - lam) * β₂ j) = (1 - lam) * (Z₂.G i j * β₂ j)),
      ← Finset.mul_sum, ← Finset.mul_sum]
    ring

end CORALean.Arithmetic.Real
