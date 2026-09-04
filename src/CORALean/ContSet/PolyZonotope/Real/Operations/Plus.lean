import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# `PolyZonotope.plus`

CORA's `@polyZonotope/plus`: centres add, and all three generator blocks
concatenate.

The exponent matrices do *not*. Each set's dependent factors range freely and
independently of the other's, so identifying them would tie the two sets
together and shrink the sum. `plusE` therefore lays the two matrices out
block-diagonally: the combined set has `p₁ + p₂` factors, and a generator that
came from one set carries exponent zero on every factor of the other, which
reads its monomial back as a monomial of its own set alone.

This is where positional factor identity costs something. CORA's `id` vector
lets `plus` *keep* a shared factor shared when the two sets are known to have
one; here `plus` always separates, which is sound and never tighter.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

/-- Two exponent matrices side by side, block-diagonally: neither set's factors
reach the other's generators. Named so that its lemmas are stated at the plain
counts `Fin (p₁ + p₂)` rather than at a projection of `plus`. -/
def PolyZonotope.plusE {p₁ h₁ p₂ h₂ : ℕ} (E₁ : Fin p₁ → Fin h₁ → ℕ)
    (E₂ : Fin p₂ → Fin h₂ → ℕ) : Fin (p₁ + p₂) → Fin (h₁ + h₂) → ℕ :=
  Fin.append (fun k => Fin.append (E₁ k) (fun _ => 0))
    (fun k => Fin.append (fun _ => 0) (E₂ k))

def PolyZonotope.plus (PZ₁ PZ₂ : PolyZonotope α) : PolyZonotope α where
  p := PZ₁.p + PZ₂.p
  h := PZ₁.h + PZ₂.h
  q := PZ₁.q + PZ₂.q
  c := PZ₁.c + PZ₂.c
  G := Fin.append PZ₁.G PZ₂.G
  E := PolyZonotope.plusE PZ₁.E PZ₂.E
  GI := Fin.append PZ₁.GI PZ₂.GI

/-- A generator from the left block sees only the left factors. Stated for an
arbitrary factor vector, since the two inclusions supply it differently: one
appends two vectors, the other restricts one. -/
theorem PolyZonotope.monomial_plusE_left {p₁ h₁ p₂ h₂ : ℕ} (E₁ : Fin p₁ → Fin h₁ → ℕ)
    (E₂ : Fin p₂ → Fin h₂ → ℕ) (a : Fin (p₁ + p₂) → ℝ) (i : Fin h₁) :
    PolyZonotope.monomial (PolyZonotope.plusE E₁ E₂) a (Fin.castAdd h₂ i)
      = PolyZonotope.monomial E₁ (fun k => a (Fin.castAdd p₂ k)) i := by
  rw [PolyZonotope.monomial, PolyZonotope.monomial, Fin.prod_univ_add]
  have hother : (∏ k : Fin p₂, a (Fin.natAdd p₁ k)
      ^ PolyZonotope.plusE E₁ E₂ (Fin.natAdd p₁ k) (Fin.castAdd h₂ i)) = 1 :=
    Finset.prod_eq_one fun k _ => by
      simp only [PolyZonotope.plusE, Fin.append_right, Fin.append_left, pow_zero]
  have hown : (∏ k : Fin p₁, a (Fin.castAdd p₂ k)
      ^ PolyZonotope.plusE E₁ E₂ (Fin.castAdd p₂ k) (Fin.castAdd h₂ i))
      = ∏ k, a (Fin.castAdd p₂ k) ^ E₁ k i :=
    Finset.prod_congr rfl fun k _ => by
      simp only [PolyZonotope.plusE, Fin.append_left]
  rw [hother, hown, mul_one]

-- the mirror on the right block, where the other set's factors contribute `1`
theorem PolyZonotope.monomial_plusE_right {p₁ h₁ p₂ h₂ : ℕ} (E₁ : Fin p₁ → Fin h₁ → ℕ)
    (E₂ : Fin p₂ → Fin h₂ → ℕ) (a : Fin (p₁ + p₂) → ℝ) (i : Fin h₂) :
    PolyZonotope.monomial (PolyZonotope.plusE E₁ E₂) a (Fin.natAdd h₁ i)
      = PolyZonotope.monomial E₂ (fun k => a (Fin.natAdd p₁ k)) i := by
  rw [PolyZonotope.monomial, PolyZonotope.monomial, Fin.prod_univ_add]
  have hother : (∏ k : Fin p₁, a (Fin.castAdd p₂ k)
      ^ PolyZonotope.plusE E₁ E₂ (Fin.castAdd p₂ k) (Fin.natAdd h₁ i)) = 1 :=
    Finset.prod_eq_one fun k _ => by
      simp only [PolyZonotope.plusE, Fin.append_left, Fin.append_right, pow_zero]
  have hown : (∏ k : Fin p₂, a (Fin.natAdd p₁ k)
      ^ PolyZonotope.plusE E₁ E₂ (Fin.natAdd p₁ k) (Fin.natAdd h₁ i))
      = ∏ k, a (Fin.natAdd p₁ k) ^ E₂ k i :=
    Finset.prod_congr rfl fun k _ => by
      simp only [PolyZonotope.plusE, Fin.append_right]
  rw [hother, hown, one_mul]

end CORALean.Real
