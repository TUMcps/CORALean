import CORALean.ContSet.PolyZonotope.Real.Operations.LinComb
import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialLinCombEFst
import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialLinCombELast
import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialLinCombESnd
import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusELeft
import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusERight
import CORALean.ContSet.Zonotope.Real.Theorems.SumPair

/-!
# What `linComb`'s witness evaluates to

The value identity behind `linComb_outer`, split out of it so that a
representation built on top of `PolyZonotope.linComb` can reuse the arithmetic
rather than restate it: the constrained polynomial zonotope's `linComb` has the
same generators and the same witness, and differs only in carrying a constraint
system along.

An identity, not an inclusion, and free in `lam`: the three dependent blocks and
the paired independent one recombine into the segment whatever the parameter is.
The unit-box side conditions are what `lam ∈ [0,1]` is needed for, and they are
stated where the inclusion is.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `Fin.sum_univ_add` at `linComb`'s dependent generator count, stated through
the projection because that is the form the goal has. Only the outermost split
needs it; every block it produces has a plain count. -/
theorem PolyZonotope.aux_sum_univ_linComb_h {pZ₁ pZ₂ : PolyZonotope α}
    (f : Fin (pZ₁.h + pZ₂.h + (pZ₁.h + pZ₂.h + 1)) → α) :
    ∑ i : Fin (pZ₁.linComb pZ₂).h, f i
      = ∑ i, f (Fin.castAdd (pZ₁.h + pZ₂.h + 1) i)
        + ∑ i, f (Fin.natAdd (pZ₁.h + pZ₂.h) i) :=
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
    ∑ i, (t * m i) • (s • G i) = (t * s) • ∑ i, m i • G i := by -- --- PROOF ---
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, smul_smul]
  congr 1
  ring


-- =======================================  MAIN THEOREM  ======================================= --

/-- The witness `linComb_outer` supplies — each set's own factors, `2λ-1` on the
fresh one, and the zonotope pairing on the independent coefficients — evaluates
to the segment point `λ y₁ + (1-λ) y₂` exactly. -/
theorem PolyZonotope.linComb_value (pZ₁ pZ₂ : PolyZonotope α) (a₁ : Fin pZ₁.p → ℝ)
    (β₁ : Fin pZ₁.q → ℝ) (a₂ : Fin pZ₂.p → ℝ) (β₂ : Fin pZ₂.q → ℝ) (lam : ℝ) :
    lam • (pZ₁.c + ∑ i, PolyZonotope.monomial pZ₁.E a₁ i • pZ₁.G i + ∑ j, β₁ j • pZ₁.GI j)
        + (1 - lam) • (pZ₂.c + ∑ i, PolyZonotope.monomial pZ₂.E a₂ i • pZ₂.G i
          + ∑ j, β₂ j • pZ₂.GI j)
      = (pZ₁.linComb pZ₂).c
        + ∑ i, PolyZonotope.monomial (pZ₁.linComb pZ₂).E
              (Fin.append (Fin.append a₁ a₂) fun _ : Fin 1 => 2 * lam - 1) i
            • (pZ₁.linComb pZ₂).G i
        + ∑ j, Fin.append (Zonotope.pairCoeffSum β₁ β₂ lam)
              (Zonotope.pairCoeffDiff β₁ β₂ lam) j • (pZ₁.linComb pZ₂).GI j := by -- --- PROOF ---
  rw [PolyZonotope.aux_sum_univ_linComb_h]
  simp only [PolyZonotope.linComb, Fin.sum_univ_add, Fin.sum_univ_one,
    PolyZonotope.monomial_linCombE_fst, PolyZonotope.monomial_linCombE_snd,
    PolyZonotope.monomial_linCombE_last, PolyZonotope.monomial_plusE_left,
    PolyZonotope.monomial_plusE_right, Fin.append_left, Fin.append_right]
  -- the three dependent blocks, each with its constant pulled out, and the pairing
  rw [PolyZonotope.aux_sum_scaled (2:ℝ)⁻¹ (PolyZonotope.monomial pZ₁.E a₁) pZ₁.G,
    PolyZonotope.aux_sum_scaled (2:ℝ)⁻¹ (PolyZonotope.monomial pZ₂.E a₂) pZ₂.G,
    PolyZonotope.aux_sum_scaled_mul (2 * lam - 1) (2:ℝ)⁻¹
      (PolyZonotope.monomial pZ₁.E a₁) pZ₁.G,
    PolyZonotope.aux_sum_scaled_mul (2 * lam - 1) (-(2:ℝ)⁻¹)
      (PolyZonotope.monomial pZ₂.E a₂) pZ₂.G,
    Zonotope.sum_pair pZ₁.GI pZ₂.GI β₁ β₂ lam]
  module

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
