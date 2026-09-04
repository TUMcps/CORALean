import CORALean.ContSet.PolyZonotope.Real.Operations.Plus
import CORALean.ContSet.Zonotope.Real.Operations.LinComb

/-!
# `PolyZonotope.linComb`

CORA's `@polyZonotope/linComb`, and the operation the representation is good at:
one fresh dependent factor `α` carries the whole segment parameter. Writing
`λ = (1+α)/2` turns `λ y₁ + (1-λ) y₂` into `½(y₁+y₂) + ½α(y₁-y₂)`, and both
halves are again polynomial in the factors, so the dependent part loses nothing
where a zonotope has to spend a generator on the centre difference.

Three dependent blocks come out of that: `½G₁ ++ ½G₂` at the original monomials,
`½G₁ ++ -½G₂` at the same monomials times `α`, and one generator `½(c₁-c₂)` at
`α` alone. `linCombE` repeats the block-diagonal `plusE` across the first two
blocks and sets the fresh factor's row to `1` on exactly the second.

The independent generators are where exactness stops: their coefficients come
out as `½(1±α)βⱼ`, which the representation cannot express, so the two blocks
are enclosed instead. That enclosure is CORA's `zonotope/enclose` at a zero
centre, which is `Zonotope.pairSum` and `Zonotope.pairDiff` — tighter than
keeping each `GIⱼ` at full width, at the same count `q₁ + q₂`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   03-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

/-- The exponent matrix of `linComb`: the two sets' factors block-diagonally as
`plus` lays them out, repeated across the two dependent blocks, and the fresh
factor last, at exponent `1` on the second block and `0` on the first. -/
def PolyZonotope.linCombE {p₁ h₁ p₂ h₂ : ℕ} (E₁ : Fin p₁ → Fin h₁ → ℕ)
    (E₂ : Fin p₂ → Fin h₂ → ℕ) :
    Fin (p₁ + p₂ + 1) → Fin (h₁ + h₂ + (h₁ + h₂ + 1)) → ℕ :=
  Fin.append
    (fun k => Fin.append (PolyZonotope.plusE E₁ E₂ k)
      (Fin.append (PolyZonotope.plusE E₁ E₂ k) (fun _ : Fin 1 => 0)))
    (fun _ : Fin 1 => Fin.append (fun _ => 0) (fun _ => 1))

noncomputable def PolyZonotope.linComb (PZ₁ PZ₂ : PolyZonotope α) : PolyZonotope α where
  p := PZ₁.p + PZ₂.p + 1
  h := PZ₁.h + PZ₂.h + (PZ₁.h + PZ₂.h + 1)
  q := PZ₁.q + PZ₂.q
  c := (2:ℝ)⁻¹ • (PZ₁.c + PZ₂.c)
  G := Fin.append
        (Fin.append (fun i => (2:ℝ)⁻¹ • PZ₁.G i) (fun i => (2:ℝ)⁻¹ • PZ₂.G i))
        (Fin.append
          (Fin.append (fun i => (2:ℝ)⁻¹ • PZ₁.G i) (fun i => (-(2:ℝ)⁻¹ : ℝ) • PZ₂.G i))
          (fun _ : Fin 1 => (2:ℝ)⁻¹ • (PZ₁.c - PZ₂.c)))
  E := PolyZonotope.linCombE PZ₁.E PZ₂.E
  GI := Fin.append (Zonotope.pairSum PZ₁.GI PZ₂.GI) (Zonotope.pairDiff PZ₁.GI PZ₂.GI)

variable {p₁ h₁ p₂ h₂ : ℕ} (E₁ : Fin p₁ → Fin h₁ → ℕ) (E₂ : Fin p₂ → Fin h₂ → ℕ)

/-- The first block keeps the monomials the two sets brought: the fresh factor
sits there at exponent zero. -/
theorem PolyZonotope.monomial_linCombE_fst (a : Fin (p₁ + p₂ + 1) → ℝ)
    (i : Fin (h₁ + h₂)) :
    PolyZonotope.monomial (PolyZonotope.linCombE E₁ E₂) a (Fin.castAdd (h₁ + h₂ + 1) i)
      = PolyZonotope.monomial (PolyZonotope.plusE E₁ E₂)
          (fun k => a (Fin.castAdd 1 k)) i := by
  rw [PolyZonotope.monomial, PolyZonotope.monomial, Fin.prod_univ_add, Fin.prod_univ_one]
  have hnew : a (Fin.natAdd (p₁ + p₂) (0 : Fin 1))
      ^ PolyZonotope.linCombE E₁ E₂ (Fin.natAdd (p₁ + p₂) (0 : Fin 1))
        (Fin.castAdd (h₁ + h₂ + 1) i) = 1 := by
    simp only [PolyZonotope.linCombE, Fin.append_right, Fin.append_left, pow_zero]
  rw [hnew, mul_one]
  exact Finset.prod_congr rfl fun k _ => by
    simp only [PolyZonotope.linCombE, Fin.append_left]

/-- The second block is the first times the fresh factor, which is the whole of
what makes `linComb` exact on the dependent part. -/
theorem PolyZonotope.monomial_linCombE_snd (a : Fin (p₁ + p₂ + 1) → ℝ)
    (i : Fin (h₁ + h₂)) :
    PolyZonotope.monomial (PolyZonotope.linCombE E₁ E₂) a
        (Fin.natAdd (h₁ + h₂) (Fin.castAdd 1 i))
      = a (Fin.natAdd (p₁ + p₂) (0 : Fin 1))
          * PolyZonotope.monomial (PolyZonotope.plusE E₁ E₂)
              (fun k => a (Fin.castAdd 1 k)) i := by
  rw [PolyZonotope.monomial, PolyZonotope.monomial, Fin.prod_univ_add, Fin.prod_univ_one]
  have hnew : a (Fin.natAdd (p₁ + p₂) (0 : Fin 1))
      ^ PolyZonotope.linCombE E₁ E₂ (Fin.natAdd (p₁ + p₂) (0 : Fin 1))
        (Fin.natAdd (h₁ + h₂) (Fin.castAdd 1 i))
      = a (Fin.natAdd (p₁ + p₂) (0 : Fin 1)) := by
    simp only [PolyZonotope.linCombE, Fin.append_right, pow_one]
  rw [hnew, mul_comm]
  refine congrArg _ (Finset.prod_congr rfl fun k _ => ?_)
  simp only [PolyZonotope.linCombE, Fin.append_left, Fin.append_right]

/-- The centre-difference generator carries the fresh factor and nothing
else. -/
theorem PolyZonotope.monomial_linCombE_last (a : Fin (p₁ + p₂ + 1) → ℝ) :
    PolyZonotope.monomial (PolyZonotope.linCombE E₁ E₂)
        (h := h₁ + h₂ + (h₁ + h₂ + 1)) a
        (Fin.natAdd (h₁ + h₂) (Fin.natAdd (h₁ + h₂) (0 : Fin 1)))
      = a (Fin.natAdd (p₁ + p₂) (0 : Fin 1)) := by
  rw [PolyZonotope.monomial, Fin.prod_univ_add, Fin.prod_univ_one]
  have hold : (∏ k : Fin (p₁ + p₂), a (Fin.castAdd 1 k)
      ^ PolyZonotope.linCombE E₁ E₂ (Fin.castAdd 1 k)
        (Fin.natAdd (h₁ + h₂) (Fin.natAdd (h₁ + h₂) (0 : Fin 1)))) = 1 :=
    Finset.prod_eq_one fun k _ => by
      simp only [PolyZonotope.linCombE, Fin.append_left, Fin.append_right, pow_zero]
  rw [hold, one_mul]
  simp only [PolyZonotope.linCombE, Fin.append_right, pow_one]

end CORALean.Real
