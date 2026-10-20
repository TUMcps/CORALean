module

public import CORALean.ContSet.PolyZonotope.Float.Operations.CubMapDep
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorError
public import CORALean.ContSet.PolyZonotope.Real.Theorems.CubEvalExpand
public import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne
public import CORALean.ContSet.Zonotope.Float.Theorems.CubContractBracket

@[expose] public section

/-!
# The cubic image of a point of `cubMapDep`'s operand, over a floating-point scalar

At the factors `a`, the point of the operand is the sum of the extended generators `[c, G]` weighted
by their monomials, and its cubic map is the sum over ordered triples of the product of the three
monomials times the contraction of the three generators (`cubEval_expand`). The monomial of a triple
is the monomial of the result's exponent column `E_a + E_b + E_c`, and each exact contraction is
within `cubMapGDiff` of the stored generator (`cubContract_bracket`), so the shortfalls, with the
monomials as coefficients in `[-1, 1]`, are in the box.

## Inputs
* `T` – family of cubic form tensors
* `pZ` – polynomial zonotope
* `a` – factor values

## Hypotheses
* `ha` – factor values are at most one

## Conclusion
* the cubic image of the point is attained up to an error-box element
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.cubMapDep_point (T : Fin m → Fin n → Mat 𝕋 n n) (pZ : PolyZonotope (Vec 𝕋 n))
    {a : Fin pZ.p → ℝ} (ha : ∀ k, |a k| ≤ 1) : -- --- CONCL ---
    ∃ e ∈ (PolyZonotope.cubMapDep T pZ).I_error.construct,
      Real.PolyZonotope.cubEval (fun i k => toRealMat (T i k))
          (fun i => toReal (pZ.c i)
            + ∑ l, toReal (pZ.G l i) * Real.PolyZonotope.monomial pZ.E a l)
        = fun i => ∑ l, toReal ((PolyZonotope.cubMapDep T pZ).G l i)
            * Real.PolyZonotope.monomial (PolyZonotope.cubMapDep T pZ).E a l
            + e i := by -- --- PROOF ---
  -- the extended columns `[c, G]`, their monomials and the point as one sum
  set Zext : Fin (pZ.h + 1) → Vec 𝕋 n := Fin.cons pZ.c pZ.G with hZext
  set w : Fin (pZ.h + 1) → ℝ := Real.PolyZonotope.monomial (PolyZonotope.extE pZ) a with hw
  have hw0 : w 0 = 1 := by simp [hw, Real.PolyZonotope.monomial, PolyZonotope.extE]
  have hws : ∀ l, w l.succ = Real.PolyZonotope.monomial pZ.E a l := fun l => by
    simp [hw, Real.PolyZonotope.monomial, PolyZonotope.extE]
  have hwabs : ∀ j, |w j| ≤ 1 := fun j =>
    Real.PolyZonotope.abs_monomial_le_one (PolyZonotope.extE pZ) ha j
  have hpt : (fun i => toReal (pZ.c i)
        + ∑ l, toReal (pZ.G l i) * Real.PolyZonotope.monomial pZ.E a l)
      = ∑ j, w j • toRealVec (Zext j) := by
    funext i
    simp [Finset.sum_apply, Fin.sum_univ_succ, hw0, hws, hZext, toRealVec, mul_comm]
  -- the stored generators against the exact contractions
  have hb := Zonotope.cubContract_bracket T
  -- the shortfall of each triple
  set Δ : Fin m → Fin ((pZ.h + 1) * (pZ.h + 1) * (pZ.h + 1)) → ℝ := fun i l =>
    (∑ k, toReal (Zext (Real.Zonotope.cubIdx _ _ _ l).1.1 k)
        * (toRealVec (Zext (Real.Zonotope.cubIdx _ _ _ l).1.2) ⬝ᵥ
          (toRealMat (T i k) *ᵥ toRealVec (Zext (Real.Zonotope.cubIdx _ _ _ l).2))))
      - toReal (PolyZonotope.cubMapGDown T pZ i l) with hΔ
  -- the monomial of each result column
  have hmon : ∀ l, Real.PolyZonotope.monomial (PolyZonotope.cubMapDep T pZ).E a l
      = w (Real.Zonotope.cubIdx _ _ _ l).1.1 * w (Real.Zonotope.cubIdx _ _ _ l).1.2
        * w (Real.Zonotope.cubIdx _ _ _ l).2 := fun l => by
    simp only [Real.PolyZonotope.monomial, PolyZonotope.cubMapDep, hw, pow_add,
      Finset.prod_mul_distrib]
    rfl
  refine ⟨fun i => ∑ l, Δ i l * Real.PolyZonotope.monomial (PolyZonotope.cubMapDep T pZ).E a l,
    PolyZonotope.mem_generatorError (G := PolyZonotope.cubMapGDiff T pZ) (fun i l => ?_)
      (fun l => ?_), ?_⟩
  · -- the shortfall is within the gap
    have b := hb (Zext (Real.Zonotope.cubIdx _ _ _ l).1.1) (Zext (Real.Zonotope.cubIdx _ _ _ l).1.2)
      (Zext (Real.Zonotope.cubIdx _ _ _ l).2) i
    have hgap := sub_le_subUp (PolyZonotope.cubMapGUp T pZ i l) (PolyZonotope.cubMapGDown T pZ i l)
    rw [abs_le]
    simp only [hΔ, PolyZonotope.cubMapGDiff]
    simp only [PolyZonotope.cubMapGDown, PolyZonotope.cubMapGUp] at hgap ⊢
    constructor <;> linarith [b.1, b.2]
  · rw [hmon]
    simp only [abs_mul]
    exact mul_le_one₀ (mul_le_one₀ (hwabs _) (abs_nonneg _) (hwabs _)) (abs_nonneg _) (hwabs _)
  · -- the expansion over triples, then over the indexed generators
    -- the point as the weighted extended generators, the cubic map expanded
    funext i
    rw [hpt, Real.PolyZonotope.cubEval_expand _ w (fun j => toRealVec (Zext j)) i]
    -- the triples as the indexed generators
    beta_reduce
    refine Eq.trans ?_ Finset.sum_add_distrib
    have hidx := Fintype.sum_equiv (Real.Zonotope.cubIdx (pZ.h + 1) (pZ.h + 1) (pZ.h + 1))
      (fun l => w (Real.Zonotope.cubIdx _ _ _ l).1.1 * w (Real.Zonotope.cubIdx _ _ _ l).1.2
        * w (Real.Zonotope.cubIdx _ _ _ l).2 * ∑ k, toRealVec (Zext
          (Real.Zonotope.cubIdx _ _ _ l).1.1) k * (toRealVec (Zext
            (Real.Zonotope.cubIdx _ _ _ l).1.2) ⬝ᵥ (toRealMat (T i k) *ᵥ toRealVec (Zext
              (Real.Zonotope.cubIdx _ _ _ l).2))))
      (fun t : (Fin (pZ.h + 1) × Fin (pZ.h + 1)) × Fin (pZ.h + 1) =>
        w t.1.1 * w t.1.2 * w t.2 * ∑ k, toRealVec (Zext t.1.1) k
          * (toRealVec (Zext t.1.2) ⬝ᵥ (toRealMat (T i k) *ᵥ toRealVec (Zext t.2))))
      (fun l => rfl)
    -- the index type is a product of three
    rw [Fintype.sum_prod_type] at hidx
    simp only [Fintype.sum_prod_type] at hidx
    -- term by term: the stored generator plus its shortfall is the exact contraction
    rw [← hidx]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hmon]
    simp only [hΔ]
    have hG : (PolyZonotope.cubMapDep T pZ).G l i = PolyZonotope.cubMapGDown T pZ i l := rfl
    rw [hG]
    simp only [toRealVec]
    ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
