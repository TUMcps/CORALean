module

public import CORALean.ContSet.Taylm.Float.Operations.TimesMerged
public import CORALean.ContSet.Taylm.Float.Theorems.AbsorbRoundingNominal
public import CORALean.ContSet.Taylm.Float.Theorems.AbsPolyOfRoundLe
public import CORALean.ContSet.Taylm.Float.Theorems.AccumTermsLe
public import CORALean.ContSet.Taylm.Float.Theorems.PolyBoundsMonoMem
public import CORALean.ContSet.Taylm.Real.Operations.Times
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfFilter
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfMulTerms

@[expose] public section

/-!
# `Taylm.timesMerged` encloses the product

## Inputs
* `N` – order the product is truncated at
* `T₁` – first Taylor model
* `T₂` – second Taylor model
* `f` – function the first encloses
* `g` – function the second encloses

## Hypotheses
* `h₁` – `T₁` encloses `f`
* `h₂` – `T₂` encloses `g`

## Conclusion
* the product model encloses `f · g`, for every order `N`
-/

-- Authors:       Claude Opus 5.5
-- Written:       20-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.timesMerged_outer (N : ℕ) {T₁ T₂ : Taylm 𝕋 n} {f g : Vec ℝ n → ℝ}
    (h₁ : T₁.Encloses f) (h₂ : T₂.Encloses g) : -- --- CONCL ---
    (Taylm.timesMerged N T₁ T₂).Encloses fun t => f t * g t := by -- --- PROOF ---
  intro t ht
  -- the names of the definition
  set r := T₁.absorbRounding.rem
  set s := T₂.absorbRounding.rem
  set p := Taylm.polyBoundsMono T₁.terms
  set q := Taylm.polyBoundsMono T₂.terms
  set P := T₁.terms.flatMap fun a => T₂.terms.map fun b => (a, b)
  set pk : (𝕋 × (Fin n → ℕ)) × (𝕋 × (Fin n → ℕ)) → Bool :=
    fun x => Nat.ble (Real.Taylm.degree (x.1.2 + x.2.2)) N
  set ex : (𝕋 × (Fin n → ℕ)) × (𝕋 × (Fin n → ℕ)) → ℝ × (Fin n → ℕ) :=
    fun x => (toReal x.1.1 * toReal x.2.1, x.1.2 + x.2.2)
  set P₁ := Real.Taylm.polyOf (T₁.terms.map fun a => (toReal a.1, a.2)) t
  set P₂ := Real.Taylm.polyOf (T₂.terms.map fun a => (toReal a.1, a.2)) t
  -- the remainders of the operands, the bounds of their polynomials
  have hr₁ := Taylm.absorbRounding_nominal h₁ t ht
  have hr₂ := Taylm.absorbRounding_nominal h₂ t ht
  simp only [Taylm.nominal, Real.Taylm.poly, show T₁.absorbRounding.terms = T₁.terms from rfl,
    show T₂.absorbRounding.terms = T₂.terms from rfl] at hr₁ hr₂
  have hp := Taylm.polyBoundsMono_mem T₁.terms ht
  have hq := Taylm.polyBoundsMono_mem T₂.terms ht
  -- the cross terms
  have m₁ := Taylm.timesZeroInf_mem (a := p) (b := s) hp.1 hp.2 hr₂.1 hr₂.2
  have m₂ := Taylm.timesZeroInf_mem (a := q) (b := r) hq.1 hq.2 hr₁.1 hr₁.2
  have m₃ := Taylm.timesZeroInf_mem (a := r) (b := s) hr₁.1 hr₁.2 hr₂.1 hr₂.2
  -- the product of the polynomials, split at the order
  have hP : Real.Taylm.polyOf (P.map ex) t = P₁ * P₂ := by
    rw [← Real.Taylm.polyOf_mulTerms]
    congr 1
    simp [P, ex, Real.Taylm.mulTerms, List.map_flatMap, List.flatMap_map]
    rfl
  have hsplit := Real.Taylm.polyOf_filter (P.map ex)
    (fun a => Nat.ble (Real.Taylm.degree a.2) N) t
  rw [List.filter_map, List.filter_map] at hsplit
  -- the kept products: their rounding, then their merge
  have rK := abs_le.1 (Taylm.abs_polyOf_round_le (P.filter pk) (fun x => mulDown x.1.1 x.2.1)
    (fun x => mulUp x.1.1 x.2.1) (fun x => (ex x).1) (fun x => x.1.2 + x.2.2)
    (fun x _ => ⟨mulDown_le_mul _ _, mul_le_mulUp _ _⟩) ht)
  have hK := abs_le.1 (Taylm.accumTerms_le []
    ((P.filter pk).map fun x => (mulUp x.1.1 x.2.1, x.1.2 + x.2.2)) ht)
  -- the dropped products, bounded into the remainder after the cross terms
  set R₀ := Taylm.sumRanges id (Taylm.timesZeroInf p s)
    [Taylm.timesZeroInf q r, Taylm.timesZeroInf r s]
  have h₀ : toReal R₀.inf ≤ P₁ * (g t - P₂) + P₂ * (f t - P₁) + (f t - P₁) * (g t - P₂) ∧
      P₁ * (g t - P₂) + P₂ * (f t - P₁) + (f t - P₁) * (g t - P₂) ≤ toReal R₀.sup := by
    have := addDown_le_add (Taylm.timesZeroInf p s).inf (Taylm.timesZeroInf q r).inf
    have := addDown_le_add (addDown (Taylm.timesZeroInf p s).inf (Taylm.timesZeroInf q r).inf)
      (Taylm.timesZeroInf r s).inf
    have := add_le_addUp (Taylm.timesZeroInf p s).sup (Taylm.timesZeroInf q r).sup
    have := add_le_addUp (addUp (Taylm.timesZeroInf p s).sup (Taylm.timesZeroInf q r).sup)
      (Taylm.timesZeroInf r s).sup
    simp only [R₀, Taylm.sumRanges, List.foldl_cons, List.foldl_nil, id]
    constructor <;> linarith [m₁.1, m₁.2, m₂.1, m₂.2, m₃.1, m₃.2]
  -- the dropped products start from the cross terms, each in its monomial's range
  have hD := Taylm.sumRanges_mem
    (fun x : (𝕋 × (Fin n → ℕ)) × (𝕋 × (Fin n → ℕ)) => Taylm.timesZeroInf
      (Taylm.monomialRange (x.1.2 + x.2.2)) ⟨mulDown x.1.1 x.2.1, mulUp x.1.1 x.2.1⟩)
    (P.filter fun x => !pk x)
    (fun x => Real.Taylm.monomial (x.1.2 + x.2.2) t * (toReal x.1.1 * toReal x.2.1)) h₀
    (fun x _ => Taylm.timesZeroInf_mem (Taylm.monomialRange_mem ht _).1
      (Taylm.monomialRange_mem ht _).2 (mulDown_le_mul _ _) (mul_le_mulUp _ _))
  -- the polynomials of the term lists, as the bounds above name them
  have eD : Real.Taylm.polyOf ((P.filter fun x => !pk x).map ex) t
      = ((P.filter fun x => !pk x).map
          fun x => Real.Taylm.monomial (x.1.2 + x.2.2) t * (toReal x.1.1 * toReal x.2.1)).sum := by
    simp only [Real.Taylm.polyOf, List.map_map, Function.comp_def, ex]
    congr 1
    exact List.map_congr_left fun a _ => mul_comm _ _
  have eK : Real.Taylm.polyOf ((P.filter pk).map fun x => ((ex x).1, x.1.2 + x.2.2)) t
      = Real.Taylm.polyOf ((P.filter pk).map ex) t := rfl
  have eU : Real.Taylm.polyOf (((P.filter pk).map fun x => (mulUp x.1.1 x.2.1, x.1.2 + x.2.2)).map
        fun a => (toReal a.1, a.2)) t
      = Real.Taylm.polyOf ((P.filter pk).map fun x => (toReal (mulUp x.1.1 x.2.1), x.1.2 + x.2.2))
        t := by
    rw [List.map_map]
    rfl
  rw [eK] at rK
  rw [eU, List.map_nil, Real.Taylm.polyOf_nil, sub_zero] at hK
  have hfg : f t * g t
      = P₁ * P₂ + (P₁ * (g t - P₂) + P₂ * (f t - P₁) + (f t - P₁) * (g t - P₂)) := by
    ring
  -- the result's names: the kept terms merged, their rounding, the remainder
  set K := Taylm.accumTerms [] ((P.filter pk).map fun x => (mulUp x.1.1 x.2.1, x.1.2 + x.2.2))
  set errK := listSumUp ((P.filter pk).map fun x => subUp (mulUp x.1.1 x.2.1) (mulDown x.1.1 x.2.1))
  set R := Taylm.sumRanges (fun x : (𝕋 × (Fin n → ℕ)) × (𝕋 × (Fin n → ℕ)) =>
    Taylm.timesZeroInf (Taylm.monomialRange (x.1.2 + x.2.2))
      ⟨mulDown x.1.1 x.2.1, mulUp x.1.1 x.2.1⟩) R₀ (P.filter fun x => !pk x)
  have herr := add_le_addUp K.2 errK
  have hsplit' : Real.Taylm.polyOf (P.map ex) t = Real.Taylm.polyOf ((P.filter pk).map ex) t
      + Real.Taylm.polyOf ((P.filter fun x => !pk x).map ex) t := hsplit
  show toReal R.inf + toReal (neg (addUp K.2 errK))
      ≤ f t * g t - Real.Taylm.polyOf (K.1.map fun a => (toReal a.1, a.2)) t ∧
    f t * g t - Real.Taylm.polyOf (K.1.map fun a => (toReal a.1, a.2)) t
      ≤ toReal R.sup + toReal (addUp K.2 errK)
  rw [toReal_neg]
  constructor <;> linarith [hD.1, hD.2, rK.1, rK.2, hK.1, hK.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
