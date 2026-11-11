module

public import CORALean.ContSet.PolyZonotope.Float.Operations.ExactPlusAlign
public import CORALean.ContSet.PolyZonotope.Float.Theorems.PlusFiber
public import CORALean.ContSet.PolyZonotope.Real.Theorems.PadBackPoint

@[expose] public section

/-!
# The fibers of an exact sum

`exactPlus` shares the factors of its two sets, so a point of the sum at the factors `a` is the sum
of a point of each at the same `a`: this is what the plain sum `plus`, with its factors side by
side, cannot say. `padBack` adds factors the set does not depend on, so its fibers are those of
the set; `exactPlusAlign` pads the set with fewer factors and shares the first `min` of them, so
one sequence `α` of factor values serves both.

## Inputs
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope
* `α` – factor values, by position
* `x` – point of the first
* `y` – point of the second

## Hypotheses
* `hx` – the first point is in the fiber of the first operand at `α`
* `hy` – the second point is in the fiber of the second operand at `α`

## Conclusion
* the sum of the points is in the fiber of the exact sum at `α`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [SoundFloatArithmetic 𝕋] in
/-- A column from the left operand keeps its own monomial. -/
private theorem PolyZonotope.aux_monomial_exactPlus_left (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n))
    (hp : pZ₁.p = pZ₂.p) (a : Fin pZ₁.p → ℝ) (i : Fin pZ₁.h) :
    Real.PolyZonotope.monomial (pZ₁.exactPlus pZ₂ hp).E a (Fin.castAdd pZ₂.h i)
      = Real.PolyZonotope.monomial pZ₁.E a i :=
  Finset.prod_congr rfl fun k _ => by
    rw [show (pZ₁.exactPlus pZ₂ hp).E k (Fin.castAdd pZ₂.h i) = pZ₁.E k i from
      Fin.append_left _ _ i]

omit [SoundFloatArithmetic 𝕋] in
/-- A column from the right operand keeps its own monomial, read at the renamed factors. -/
private theorem PolyZonotope.aux_monomial_exactPlus_right (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n))
    (hp : pZ₁.p = pZ₂.p) (a : Fin pZ₁.p → ℝ) (i : Fin pZ₂.h) : -- --- CONCL ---
    Real.PolyZonotope.monomial (pZ₁.exactPlus pZ₂ hp).E a (Fin.natAdd pZ₁.h i)
      = Real.PolyZonotope.monomial pZ₂.E (fun k => a (Fin.cast hp.symm k)) i := by -- --- PROOF ---
  show ∏ k, a k ^ (pZ₁.exactPlus pZ₂ hp).E k (Fin.natAdd pZ₁.h i)
      = ∏ k, a (Fin.cast hp.symm k) ^ pZ₂.E k i
  have hcol : ∀ k, (pZ₁.exactPlus pZ₂ hp).E k (Fin.natAdd pZ₁.h i)
      = pZ₂.E (Fin.cast hp k) i := fun k => Fin.append_right _ _ i
  rw [Finset.prod_congr rfl fun k _ => by rw [hcol k]]
  exact Fintype.prod_equiv (finCongr hp) _ _ fun _ => rfl

/-- The appended factors sit at exponent zero. -/
private theorem PolyZonotope.aux_monomial_padBack {p s : ℕ} (E : Fin p → Fin s → ℕ) (r : ℕ)
    (a : Fin (p + r) → ℝ) (i : Fin s) : -- --- CONCL ---
    Real.PolyZonotope.monomial (Real.PolyZonotope.padE E r) a i
      = Real.PolyZonotope.monomial E (a ∘ Fin.castAdd r) i := by -- --- PROOF ---
  rw [Real.PolyZonotope.monomial, Real.PolyZonotope.monomial, Fin.prod_univ_add]
  have hnew : (∏ k : Fin r, a (Fin.natAdd p k)
      ^ Real.PolyZonotope.padE E r (Fin.natAdd p k) i) = 1 :=
    Finset.prod_eq_one fun k _ => by
      simp only [Real.PolyZonotope.padE, Fin.append_right, pow_zero]
  have hold : (∏ k : Fin p, a (Fin.castAdd r k)
      ^ Real.PolyZonotope.padE E r (Fin.castAdd r k) i)
      = ∏ k, (a ∘ Fin.castAdd r) k ^ E k i :=
    Finset.prod_congr rfl fun k _ => by
      simp only [Real.PolyZonotope.padE, Fin.append_left, Function.comp_apply]
  rw [hnew, hold, mul_one]

/-- The sum of a fiber point of each, at one common `a`, is a fiber point of `exactPlus`. -/
private theorem PolyZonotope.aux_exactPlus_fiber (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n))
    (hp : pZ₁.p = pZ₂.p)
    {a : Fin pZ₁.p → ℝ} {x y : Vec ℝ n} (hx : x ∈ pZ₁.fiber a)
    (hy : y ∈ pZ₂.fiber (fun k => a (Fin.cast hp.symm k))) : -- --- CONCL ---
    x + y ∈ (pZ₁.exactPlus pZ₂ hp).fiber a := by -- --- PROOF ---
  obtain ⟨β₁, hβ₁, e₁, he₁, rfl⟩ := (PolyZonotope.mem_fiber_iff _ _ _).mp hx
  obtain ⟨β₂, hβ₂, e₂, he₂, rfl⟩ := (PolyZonotope.mem_fiber_iff _ _ _).mp hy
  -- the rounding of the center sum is a point of the residual
  set r : Vec ℝ n := fun i => toReal (pZ₁.c i) + toReal (pZ₂.c i)
    - toReal ((pZ₁.exactPlus pZ₂ hp).c i) with hr
  refine (PolyZonotope.mem_fiber_iff _ _ _).mpr ⟨Fin.append β₁ β₂, ?_, e₁ + e₂ + r, ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_)
    · simpa using hβ₁ j
    · simpa using hβ₂ j
  · exact Interval.plus_outer _ _ ⟨e₁ + e₂, Interval.plus_outer _ _ ⟨e₁, he₁, e₂, he₂, rfl⟩,
      r, Interval.sub_mem_residual (fun i => ⟨addDown_le_add _ _, add_le_addUp _ _⟩), rfl⟩
  · funext i
    -- the dependent generators are those of both, at the shared factors
    have hG : ∑ l : Fin (pZ₁.exactPlus pZ₂ hp).h, toReal ((pZ₁.exactPlus pZ₂ hp).G l i)
        * Real.PolyZonotope.monomial (pZ₁.exactPlus pZ₂ hp).E a l
        = (∑ l, toReal (pZ₁.G l i) * Real.PolyZonotope.monomial pZ₁.E a l)
          + ∑ l, toReal (pZ₂.G l i) * Real.PolyZonotope.monomial pZ₂.E
            (fun k => a (Fin.cast hp.symm k)) l := by
      rw [show (∑ l : Fin (pZ₁.exactPlus pZ₂ hp).h, _) = ∑ l : Fin (pZ₁.h + pZ₂.h), _ from rfl,
        Fin.sum_univ_add]
      congr 1
      · refine Finset.sum_congr rfl fun l _ => ?_
        rw [PolyZonotope.aux_monomial_exactPlus_left]
        simp only [PolyZonotope.exactPlus, Fin.append_left]
      · refine Finset.sum_congr rfl fun l _ => ?_
        rw [PolyZonotope.aux_monomial_exactPlus_right]
        simp only [PolyZonotope.exactPlus, Fin.append_right]
    -- the independent generators are side by side
    have hGI : ∑ j : Fin (pZ₁.exactPlus pZ₂ hp).q, toReal ((pZ₁.exactPlus pZ₂ hp).GI j i)
        * Fin.append β₁ β₂ j
        = (∑ j, toReal (pZ₁.GI j i) * β₁ j) + ∑ j, toReal (pZ₂.GI j i) * β₂ j := by
      rw [show (∑ j : Fin (pZ₁.exactPlus pZ₂ hp).q, _) = ∑ j : Fin (pZ₁.q + pZ₂.q), _ from rfl,
        Fin.sum_univ_add]
      simp only [PolyZonotope.exactPlus, Fin.append_left, Fin.append_right]
    repeat rw [PolyZonotope.nominal_point_eq]
    simp only [Pi.add_apply]
    rw [hG, hGI]
    simp only [hr]
    ring

/-- Padding with factors the set does not depend on leaves its fibers: a fiber point at the first
factors is one at all of them. -/
private theorem PolyZonotope.aux_padBack_fiber (r : ℕ) (pZ : PolyZonotope (Vec 𝕋 n))
    {a : Fin (pZ.padBack r).p → ℝ} {x : Vec ℝ n}
    (hx : x ∈ pZ.fiber (fun k => a (Fin.castAdd r k))) : -- --- CONCL ---
    x ∈ (pZ.padBack r).fiber a := by -- --- PROOF ---
  obtain ⟨β, hβ, e, he, rfl⟩ := (PolyZonotope.mem_fiber_iff _ _ _).mp hx
  refine (PolyZonotope.mem_fiber_iff _ _ _).mpr ⟨β, hβ, e, he, ?_⟩
  funext i
  have hG : ∑ l : Fin (pZ.padBack r).h, toReal ((pZ.padBack r).G l i)
      * Real.PolyZonotope.monomial (pZ.padBack r).E a l
      = ∑ l, toReal (pZ.G l i) * Real.PolyZonotope.monomial pZ.E
        (fun k => a (Fin.castAdd r k)) l :=
    Finset.sum_congr rfl fun l _ => by
      show _ * Real.PolyZonotope.monomial (Real.PolyZonotope.padE pZ.E r) a l = _
      rw [PolyZonotope.aux_monomial_padBack]
      rfl
  repeat rw [PolyZonotope.nominal_point_eq]
  simp only [Pi.add_apply]
  rw [hG]
  rfl


-- =======================================  MAIN THEOREM  ======================================= --

/-- Two sets' fiber points at one sequence of factor values `α`, by position, add to a fiber point
of the aligned exact sum at `α`. -/
theorem PolyZonotope.exactPlusAlign_fiber (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)) (α : ℕ → ℝ)
    {x y : Vec ℝ n} (hx : x ∈ pZ₁.fiber (fun k => α k))
    (hy : y ∈ pZ₂.fiber (fun k => α k)) : -- --- CONCL ---
    x + y ∈ (pZ₁.exactPlusAlign pZ₂).fiber (fun k => α k) := by -- --- PROOF ---
  generalize hR : pZ₁.exactPlusAlign pZ₂ = R
  unfold PolyZonotope.exactPlusAlign at hR
  split_ifs at hR with h
  · subst hR
    exact PolyZonotope.aux_exactPlus_fiber _ _ _ (PolyZonotope.aux_padBack_fiber _ pZ₁ hx) hy
  · subst hR
    exact PolyZonotope.aux_exactPlus_fiber _ _ _ hx (PolyZonotope.aux_padBack_fiber _ pZ₂ hy)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
