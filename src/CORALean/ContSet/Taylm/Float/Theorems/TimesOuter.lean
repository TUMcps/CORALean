module

public import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners
public import CORALean.ContSet.Taylm.Float.Operations.Times
public import CORALean.ContSet.Taylm.Float.Theorems.AbsPolyOfRoundLe
public import CORALean.ContSet.Taylm.Float.Theorems.PolyBoundsMem
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfFilter
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfMulTerms
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import CORALean.ContSet.Taylm.Float.Theorems.AbsorbRoundingNominal

@[expose] public section

/-!
# `Taylm.times` encloses the product

The exact layer's decomposition `fg - kept = dropped + p₁(g - p₂) + p₂(f - p₁) + (f - p₁)(g - p₂)`
for the two operands with their boxes absorbed (`absorbRounding_nominal`, so their remainders alone
enclose), with two more summands, the rounding of the kept and of the dropped coefficient products,
each bounded by `abs_polyOf_round_le`, the kept one the result's error box, and every sum of the
remainder rounded outward.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.times_outer {T₁ T₂ : Taylm 𝕋 n} {f g : Vec ℝ n → ℝ} (h₁ : T₁.Encloses f)
    (h₂ : T₂.Encloses g) : (T₁.times T₂).Encloses fun t => f t * g t := by -- --- PROOF ---
  intro t ht
  -- the pairs, their exact products, and the split by degree
  set N := max T₁.maxOrder T₂.maxOrder
  set P := T₁.terms.flatMap fun a => T₂.terms.map fun b => (a, b)
  set pk : (𝕋 × (Fin n → ℕ)) × (𝕋 × (Fin n → ℕ)) → Bool :=
    fun p => Nat.ble (Real.Taylm.degree (p.1.2 + p.2.2)) N
  set ex : (𝕋 × (Fin n → ℕ)) × (𝕋 × (Fin n → ℕ)) → ℝ × (Fin n → ℕ) :=
    fun p => (toReal p.1.1 * toReal p.2.1, p.1.2 + p.2.2)
  have hP : Real.Taylm.polyOf (P.map ex) t
      = Real.Taylm.polyOf (T₁.terms.map fun a => (toReal a.1, a.2)) t
        * Real.Taylm.polyOf (T₂.terms.map fun a => (toReal a.1, a.2)) t := by
    rw [← Real.Taylm.polyOf_mulTerms]
    congr 1
    simp [P, ex, Real.Taylm.mulTerms, List.map_flatMap, List.flatMap_map]
    rfl
  have hsplit := Real.Taylm.polyOf_filter (P.map ex)
    (fun a => Nat.ble (Real.Taylm.degree a.2) N) t
  rw [List.filter_map, List.filter_map] at hsplit
  -- every exact coefficient product between its two roundings
  have hc : ∀ p ∈ P,
      toReal (mulDown p.1.1 p.2.1) ≤ (ex p).1 ∧ (ex p).1 ≤ toReal (mulUp p.1.1 p.2.1) :=
    fun p _ => ⟨mulDown_le_mul _ _, mul_le_mulUp _ _⟩
  -- what storing the upper rounding costs, kept and dropped
  have rK := abs_le.1 (Taylm.abs_polyOf_round_le (P.filter pk) (fun p => mulDown p.1.1 p.2.1)
    (fun p => mulUp p.1.1 p.2.1) (fun p => (ex p).1) (fun p => p.1.2 + p.2.2)
    (fun p hp => hc p (List.mem_of_mem_filter hp)) ht)
  have rD := abs_le.1 (Taylm.abs_polyOf_round_le (P.filter fun p => !pk p)
    (fun p => mulDown p.1.1 p.2.1)
    (fun p => mulUp p.1.1 p.2.1) (fun p => (ex p).1) (fun p => p.1.2 + p.2.2)
    (fun p hp => hc p (List.mem_of_mem_filter hp)) ht)
  have hD := Taylm.polyBounds_mem ((P.filter fun p => !pk p).map
    fun p => (mulUp p.1.1 p.2.1, p.1.2 + p.2.2)) ht
  have hP₁ := Taylm.polyBounds_mem T₁.terms ht
  have hP₂ := Taylm.polyBounds_mem T₂.terms ht
  -- the cross terms, as at the exact layer
  have hr₁ := Taylm.absorbRounding_nominal h₁ t ht
  have hr₂ := Taylm.absorbRounding_nominal h₂ t ht
  simp only [Taylm.nominal, Taylm.absorbRounding, Real.Taylm.poly] at hr₁ hr₂
  have m₁ := Interval.mul_between_corners hP₁.1 hP₁.2 hr₂.1 hr₂.2
  have m₂ := Interval.mul_between_corners hP₂.1 hP₂.2 hr₁.1 hr₁.2
  have m₃ := Interval.mul_between_corners hr₁.1 hr₁.2 hr₂.1 hr₂.2
  simp only [List.map_map, Function.comp_def] at hD rK rD hsplit
  -- the dropped terms' bound, widened by their rounding
  have q₁ := subDown_le_sub (Taylm.polyBounds ((P.filter fun p => !pk p).map
    fun p => (mulUp p.1.1 p.2.1, p.1.2 + p.2.2))).inf
    (listSumUp ((P.filter fun p => !pk p).map
      fun p => subUp (mulUp p.1.1 p.2.1) (mulDown p.1.1 p.2.1)))
  have q₂ := add_le_addUp (Taylm.polyBounds ((P.filter fun p => !pk p).map
    fun p => (mulUp p.1.1 p.2.1, p.1.2 + p.2.2))).sup
    (listSumUp ((P.filter fun p => !pk p).map
      fun p => subUp (mulUp p.1.1 p.2.1) (mulDown p.1.1 p.2.1)))
  simp only [Taylm.times, Taylm.inflated, Taylm.absorbRounding, Real.Taylm.poly, List.map_map,
    Function.comp_def, toReal_neg]
  -- each end: unwind the directed sums, then the decomposition of `fg - kept`
  refine ⟨?_, ?_⟩
  · rw [← sub_eq_add_neg]
    refine le_trans (sub_le_sub_right
      (le_trans (addDown_le_add _ _) (add_le_add (le_trans (addDown_le_add _ _)
        (add_le_add (le_trans (addDown_le_add _ _) (add_le_add (subDown_le_sub _ _) le_rfl))
          le_rfl)) le_rfl)) _) ?_
    simp only [N, P, pk, ex] at *
    linarith [m₁.1, m₂.1, m₃.1, hD.1, rK.1, rD.1, q₁]
  · refine le_trans ?_ (add_le_add (le_trans (add_le_add (le_trans
      (add_le_add (le_trans (add_le_add (add_le_addUp _ _) le_rfl) (add_le_addUp _ _)) le_rfl)
        (add_le_addUp _ _)) le_rfl) (add_le_addUp _ _)) le_rfl)
    simp only [N, P, pk, ex] at *
    linarith [m₁.2, m₂.2, m₃.2, hD.2, rK.2, rD.2, q₂]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
