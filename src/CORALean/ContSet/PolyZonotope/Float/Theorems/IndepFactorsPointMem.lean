module

public import CORALean.ContSet.PolyZonotope.Float.Operations.IndepFactors
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.PolyZonotope.Real.Operations.MonomialIdentE
public import CORALean.ContSet.PolyZonotope.Real.Operations.Point
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusELeft
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusERight

@[expose] public section

/-!
# The point map of `indepFactors` stays in the nominal set

At a factor vector `(α, β)` of the unit box, the dependent point of `indepFactors` is the
nominal set's point at `α` plus `GI β`: the left block of the exponent matrix sees the factors
`α` alone (`monomial_plusE_left`), the right block is the identity on `β`
(`monomial_plusE_right`, `monomial_identE`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.indepFactors_point_mem (pZ : PolyZonotope (Vec 𝕋 n))
    {a : Fin (pZ.p + pZ.q) → ℝ} (ha : ∀ k, |a k| ≤ 1) :
    (PolyZonotope.nominal pZ.indepFactors).point a ∈
      InflatedContSet.nominalSet pZ := by -- --- PROOF ---
  refine PolyZonotope.mem_nominalSet_iff.mpr ⟨fun k => a (Fin.castAdd pZ.q k),
    fun j => a (Fin.natAdd pZ.p j), fun k => ha _, fun j => ha _, fun i => ?_⟩
  -- the two blocks of the sum, the dependent one and the freed independent one
  simp only [Real.PolyZonotope.point, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  show toReal (pZ.c i) + ∑ l : Fin (pZ.h + pZ.q), Real.PolyZonotope.monomial
      (Real.PolyZonotope.plusE pZ.E (Real.PolyZonotope.identE pZ.q)) a l
        * toReal (Fin.append pZ.G pZ.GI l i) = _
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Real.PolyZonotope.monomial_plusE_left,
    Real.PolyZonotope.monomial_plusE_right, Real.PolyZonotope.monomial_identE]
  rw [← add_assoc]
  exact congrArg₂ (· + ·) (congrArg₂ (· + ·) rfl
    (Finset.sum_congr rfl fun _ _ => mul_comm _ _))
    (Finset.sum_congr rfl fun _ _ => mul_comm _ _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
