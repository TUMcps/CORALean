module

public import CORALean.ContSet.Interval.Float.Theorems.LinCombOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Interval.Float.Theorems.OriginExact
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.PolyZonotope.Float.Operations.EncloseShared
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorErrorMonomial
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne
public import CORALean.ContSet.Zonotope.Float.Theorems.LinCombOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Float.Theorems.PickOuter

@[expose] public section

/-!
# `enclose` on shared factors encloses both sets

At the value `σ` of the new factor the dependent generators give the point
`½(c₁+c₂) + σ ½(c₁-c₂) + Σ (½(gᵢ₁+gᵢ₂) + σ ½(gᵢ₁-gᵢ₂)) mᵢ`, which is the first set's dependent part
at `σ = 1` and the second's at `σ = -1`; the stored generators differ from these by the gaps, and
the new factor and the monomials are at most one. The independent parts pair as in `convHull`.

## Inputs
* `A` – first polynomial zonotope
* `B` – second polynomial zonotope

## Hypotheses
* `hp` – both have the same number of factors
* `hh` – both have the same number of dependent generators
* `hE` – both have the same exponent matrix
* `hA` – the error box of `A` is not empty
* `hB` – the error box of `B` is not empty

## Conclusion
* the union of the two sets is contained in `encloseShared`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The monomials of the enclosure's exponents at the factors `a` and the new one `σ`. -/
private theorem PolyZonotope.aux_monomial_enclose {p h : ℕ} (E : Fin p → Fin h → ℕ)
    (a : Fin p → ℝ) (σ : ℝ) : -- --- CONCL ---
    (∀ l, Real.PolyZonotope.monomial (PolyZonotope.step_encloseE E) (Fin.snoc a σ)
        (Fin.castAdd 1 (Fin.castAdd h l)) = Real.PolyZonotope.monomial E a l)
    ∧ (∀ l, Real.PolyZonotope.monomial (PolyZonotope.step_encloseE E) (Fin.snoc a σ)
        (Fin.castAdd 1 (Fin.natAdd h l)) = Real.PolyZonotope.monomial E a l * σ)
    ∧ Real.PolyZonotope.monomial (PolyZonotope.step_encloseE E) (Fin.snoc a σ)
        (Fin.natAdd (h + h) (0 : Fin 1)) = σ := by -- --- PROOF ---
  refine ⟨fun l => ?_, fun l => ?_, ?_⟩
  all_goals
    simp only [Real.PolyZonotope.monomial, PolyZonotope.step_encloseE, Fin.prod_univ_castSucc,
      Fin.snoc_castSucc, Fin.snoc_last, Fin.lastCases_castSucc, Fin.lastCases_last,
      Fin.append_left, Fin.append_right, pow_zero, mul_one, one_mul, pow_one, Finset.prod_const_one]


/-- A halved sum and its rounding down: the stored value is below the exact one by at most the gap
of the two directed halvings. -/
private theorem PolyZonotope.aux_half_sum (x y : 𝕋) : -- --- CONCL ---
    0 ≤ (toReal x + toReal y) / 2 - toReal (half (addDown x y))
    ∧ (toReal x + toReal y) / 2 - toReal (half (addDown x y))
      ≤ toReal (subUp (half (addUp x y)) (half (addDown x y))) := by -- --- PROOF ---
  have h1 := addDown_le_add x y
  have h2 := add_le_addUp x y
  have h3 := sub_le_subUp (half (addUp x y)) (half (addDown x y))
  simp only [toReal_half] at h3 ⊢
  constructor <;> linarith

/-- The same for a halved difference. -/
private theorem PolyZonotope.aux_half_diff (x y : 𝕋) : -- --- CONCL ---
    0 ≤ (toReal x - toReal y) / 2 - toReal (half (subDown x y))
    ∧ (toReal x - toReal y) / 2 - toReal (half (subDown x y))
      ≤ toReal (subUp (half (subUp x y)) (half (subDown x y))) := by -- --- PROOF ---
  have h1 := subDown_le_sub x y
  have h2 := sub_le_subUp x y
  have h3 := sub_le_subUp (half (subUp x y)) (half (subDown x y))
  simp only [toReal_half] at h3 ⊢
  constructor <;> linarith

/-- The point of the stored enclosure at the new factor `σ`, against the exact one: they differ by
a point of the center's residual and of the generators' error box. -/
private theorem PolyZonotope.aux_core {p h : ℕ} (c₁ c₂ : Vec 𝕋 n) (g₁ g₂ : Fin h → Vec 𝕋 n)
    (E : Fin p → Fin h → ℕ) (a : Fin p → ℝ) (ha : ∀ k, |a k| ≤ 1) (σ : ℝ)
    (hσ : |σ| ≤ 1) : -- --- CONCL ---
    ∃ d ∈ (PolyZonotope.midpointResidual c₁ c₂).toSet,
      ∃ f ∈ (PolyZonotope.generatorError
          fun i l => PolyZonotope.step_encloseGap c₁ c₂ g₁ g₂ l i).toSet, ∀ i,
      (toReal (c₁ i) + toReal (c₂ i)) / 2 + σ * ((toReal (c₁ i) - toReal (c₂ i)) / 2)
        + ∑ l, ((toReal (g₁ l i) + toReal (g₂ l i)) / 2
            + σ * ((toReal (g₁ l i) - toReal (g₂ l i)) / 2)) * Real.PolyZonotope.monomial E a l
      = toReal (PolyZonotope.midpoint c₁ c₂ i)
        + ∑ l, toReal (PolyZonotope.step_encloseGen c₁ c₂ g₁ g₂ l i)
            * Real.PolyZonotope.monomial (PolyZonotope.step_encloseE E) (Fin.snoc a σ) l
        + d i + f i := by -- --- PROOF ---
  obtain ⟨hm1, hm2, hm3⟩ := PolyZonotope.aux_monomial_enclose E a σ
  have hmono : ∀ l, |Real.PolyZonotope.monomial E a l| ≤ 1 := fun l =>
    Real.PolyZonotope.abs_monomial_le_one E ha l
  -- the exact and the stored value of each generator, and the coefficient it carries
  let Δ : Mat ℝ n (h + h + 1) := fun i => Fin.append (Fin.append
    (fun l => (toReal (g₁ l i) + toReal (g₂ l i)) / 2
      - toReal (PolyZonotope.midpoint (g₁ l) (g₂ l) i))
    (fun l => (toReal (g₁ l i) - toReal (g₂ l i)) / 2
      - toReal (PolyZonotope.halfDiff (g₁ l) (g₂ l) i)))
    (fun _ => (toReal (c₁ i) - toReal (c₂ i)) / 2 - toReal (PolyZonotope.halfDiff c₁ c₂ i))
  let t : Vec ℝ (h + h + 1) := Fin.append (Fin.append (fun l => Real.PolyZonotope.monomial E a l)
    (fun l => σ * Real.PolyZonotope.monomial E a l)) (fun _ => σ)
  -- each generator's gap is bounded by the gap of its rounded sum or difference
  have hG : ∀ i l, |Δ i l| ≤ toReal (PolyZonotope.step_encloseGap c₁ c₂ g₁ g₂ l i) := by
    intro i l
    refine Fin.addCases (fun l => ?_) (fun l => ?_) l
    · refine Fin.addCases (fun l => ?_) (fun l => ?_) l
      · simp only [Δ, PolyZonotope.step_encloseGap, Fin.append_left, PolyZonotope.midpoint,
          PolyZonotope.halfDiff]
        obtain ⟨h0, h1⟩ := PolyZonotope.aux_half_sum (g₁ l i) (g₂ l i)
        rw [abs_of_nonneg h0]
        exact h1
      · simp only [Δ, PolyZonotope.step_encloseGap, Fin.append_left, Fin.append_right,
          PolyZonotope.midpoint, PolyZonotope.halfDiff]
        obtain ⟨h0, h1⟩ := PolyZonotope.aux_half_diff (g₁ l i) (g₂ l i)
        rw [abs_of_nonneg h0]
        exact h1
    · simp only [Δ, PolyZonotope.step_encloseGap, Fin.append_right, PolyZonotope.midpoint,
        PolyZonotope.halfDiff]
      obtain ⟨h0, h1⟩ := PolyZonotope.aux_half_diff (c₁ i) (c₂ i)
      rw [abs_of_nonneg h0]
      exact h1
  -- the coefficients of the generators are at most one
  have ht : ∀ l, |t l| ≤ 1 := by
    intro l
    refine Fin.addCases (fun l => ?_) (fun l => ?_) l
    · refine Fin.addCases (fun l => ?_) (fun l => ?_) l
      · simpa only [t, Fin.append_left] using hmono l
      · simp only [t, Fin.append_left, Fin.append_right]
        rw [abs_mul]
        exact mul_le_one₀ hσ (abs_nonneg _) (hmono l)
    · simpa only [t, Fin.append_right] using hσ
  refine ⟨fun i => (toReal (c₁ i) + toReal (c₂ i)) / 2 - toReal (PolyZonotope.midpoint c₁ c₂ i),
    Interval.sub_mem_residual (fun i => ⟨?_, ?_⟩), _, PolyZonotope.mem_generatorError hG ht,
    fun i => ?_⟩
  · simp only [toReal_half]
    linarith [addDown_le_add (c₁ i) (c₂ i)]
  · simp only [toReal_half]
    linarith [add_le_addUp (c₁ i) (c₂ i)]
  · -- the sums over the three blocks
    simp only [Fin.sum_univ_add, Δ, t, Fin.append_left, Fin.append_right, hm1, hm2,
      PolyZonotope.step_encloseGen]
    have hm3' : Real.PolyZonotope.monomial (PolyZonotope.step_encloseE E) (Fin.snoc a σ)
        (Fin.natAdd (h + h) (default : Fin 1)) = σ := hm3
    simp only [Finset.univ_unique, Finset.sum_singleton, hm3']
    -- the four sums at each generator are the exact value's, termwise
    have hsum : ∑ l : Fin h, ((toReal (g₁ l i) + toReal (g₂ l i)) / 2
        + σ * ((toReal (g₁ l i) - toReal (g₂ l i)) / 2)) * Real.PolyZonotope.monomial E a l
      = ∑ l : Fin h, (toReal (PolyZonotope.midpoint (g₁ l) (g₂ l) i)
            * Real.PolyZonotope.monomial E a l
          + toReal (PolyZonotope.halfDiff (g₁ l) (g₂ l) i)
            * (Real.PolyZonotope.monomial E a l * σ)
          + (((toReal (g₁ l i) + toReal (g₂ l i)) / 2
              - toReal (PolyZonotope.midpoint (g₁ l) (g₂ l) i))
              * Real.PolyZonotope.monomial E a l
            + ((toReal (g₁ l i) - toReal (g₂ l i)) / 2
              - toReal (PolyZonotope.halfDiff (g₁ l) (g₂ l) i))
              * (σ * Real.PolyZonotope.monomial E a l))) :=
      Finset.sum_congr rfl fun l _ => by ring
    rw [hsum]
    simp only [Finset.sum_add_distrib]
    ring


/-- The origin is a point of the zonotope about it with the generators `GI`, and so is every
combination of them. -/
private theorem PolyZonotope.aux_ind_mem {q : ℕ} (GI : Fin q → Vec 𝕋 n) {β : Fin q → ℝ}
    (hβ : ∀ j, |β j| ≤ 1) : -- --- CONCL ---
    (fun i => ∑ j, toReal (GI j i) * β j)
      ∈ (⟨q, fun _ => zero, GI, Interval.origin n⟩ :
        Zonotope (Vec 𝕋 n)).toSet := by -- --- PROOF ---
  have h0 : (0 : Vec ℝ n) ∈ (Interval.origin n : Interval (Vec 𝕋 n)).toSet := by
    rw [Interval.origin_exact]
    exact Set.mem_singleton _
  have hz : (fun i => ∑ j, toReal (GI j i) * β j) + 0
      ∈ InflatedContSet.nominalSet (⟨q, fun _ => zero, GI, Interval.origin n⟩ :
          Zonotope (Vec 𝕋 n)) + (Interval.origin n : Interval (Vec 𝕋 n)).toSet :=
    Set.add_mem_add (Zonotope.mem_nominalSet_iff.mpr ⟨β, hβ, fun i => by
      simp [toReal_zero]⟩) h0
  rw [add_zero] at hz
  exact hz

/-- The reordered enclosure of the independent parts holds what `Zonotope.linComb` holds. -/
private theorem PolyZonotope.aux_indep_outer (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) {x : Vec ℝ n}
    (hx : x ∈ (Zonotope.linComb Z₁ Z₂).toSet) :
    x ∈ (PolyZonotope.step_encloseIndep Z₁ Z₂).toSet := by
  unfold PolyZonotope.step_encloseIndep
  split_ifs
  · exact Zonotope.pick_outer _ _ _ hx
  · exact hx

/-- The assembly: the exact dependent part at `σ`, an independent point of the enclosure, and an
error point of the hull of the two boxes land in the stored enclosure. -/
private theorem PolyZonotope.aux_assemble (A B : PolyZonotope (Vec 𝕋 n)) (hh : B.h = A.h)
    {a : Fin A.p → ℝ} (ha : ∀ k, |a k| ≤ 1) {σ : ℝ} (hσ : |σ| ≤ 1) {zi e z0 : Vec ℝ n}
    (hzi : zi ∈ (PolyZonotope.step_encloseIndep (⟨A.q, fun _ => zero, A.GI, Interval.origin n⟩ :
        Zonotope (Vec 𝕋 n)) ⟨B.q, fun _ => zero, B.GI, Interval.origin n⟩).toSet)
    (he : e ∈ (A.I_error.linComb B.I_error).toSet)
    (hz0 : ∀ i, z0 i = (toReal (A.c i) + toReal (B.c i)) / 2
        + σ * ((toReal (A.c i) - toReal (B.c i)) / 2)
        + ∑ l, ((toReal (A.G l i) + toReal (B.G (Fin.cast hh.symm l) i)) / 2
            + σ * ((toReal (A.G l i) - toReal (B.G (Fin.cast hh.symm l) i)) / 2))
          * Real.PolyZonotope.monomial A.E a l) : -- --- CONCL ---
    z0 + zi + e ∈ (A.encloseShared B hh).toSet := by -- --- PROOF ---
  obtain ⟨d, hd, f, hf, heq⟩ := PolyZonotope.aux_core A.c B.c A.G
    (fun l => B.G (Fin.cast hh.symm l)) A.E a ha σ hσ
  obtain ⟨nZ, hnZ, eZ, heZ, rfl⟩ := hzi
  obtain ⟨β', hβ', hnZeq⟩ := Zonotope.mem_nominalSet_iff.mp hnZ
  have ha' : ∀ k : Fin (A.p + 1), |(Fin.snoc (α := fun _ => ℝ) a σ : Fin (A.p + 1) → ℝ) k| ≤ 1 := by
    intro k
    refine Fin.lastCases ?_ (fun k' => ?_) k
    · simpa using hσ
    · simpa using ha k'
  -- the enclosure of the two independent parts, as the definition forms it
  let Z : Zonotope (Vec 𝕋 n) := PolyZonotope.step_encloseIndep
    ⟨A.q, fun _ => zero, A.GI, Interval.origin n⟩ ⟨B.q, fun _ => zero, B.GI, Interval.origin n⟩
  -- the dependent point, the independent point and the error point
  refine Set.mem_add.mpr ⟨fun i => toReal (PolyZonotope.midpoint A.c B.c i)
      + ∑ l : Fin (A.h + A.h + 1), toReal (PolyZonotope.step_encloseGen A.c B.c A.G
          (fun l => B.G (Fin.cast hh.symm l)) l i)
        * Real.PolyZonotope.monomial (PolyZonotope.step_encloseE A.E) (Fin.snoc a σ) l
      + ∑ j, toReal (Z.G j i) * β' j,
    PolyZonotope.mem_nominalSet_iff.mpr
    ⟨Fin.snoc (α := fun _ => ℝ) a σ, β', ha', hβ', fun _ => rfl⟩,
    (e + d) + (f + (eZ + fun i => toReal (Z.c i))),
    Interval.plus_outer _ _ (Set.add_mem_add (Interval.plus_outer _ _ (Set.add_mem_add he hd))
      (Interval.plus_outer _ _ (Set.add_mem_add hf (Interval.plus_outer _ _
        (Set.add_mem_add heZ (Interval.mem_point _)))))), ?_⟩
  -- the coordinates agree
  funext i
  have h1 := hnZeq i
  have h2 := heq i
  simp only [Pi.add_apply]
  rw [hz0 i, h1, h2]
  ring


/-- The origin is a point of the zonotope about it. -/
private theorem PolyZonotope.aux_zero_mem {q : ℕ} (GI : Fin q → Vec 𝕋 n) :
    (0 : Vec ℝ n) ∈ (⟨q, fun _ => zero, GI, Interval.origin n⟩ : Zonotope (Vec 𝕋 n)).toSet := by
  have h := PolyZonotope.aux_ind_mem GI (β := fun _ => 0) (fun _ => by simp)
  simp only [mul_zero, Finset.sum_const_zero] at h
  exact h


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.encloseShared_outer (A B : PolyZonotope (Vec 𝕋 n)) (hp : B.p = A.p)
    (hh : B.h = A.h) (hE : HEq B.E A.E) (hA : A.I_error.toSet.Nonempty)
    (hB : B.I_error.toSet.Nonempty) : -- --- CONCL ---
    A.toSet ∪ B.toSet ⊆ (A.encloseShared B hh).toSet := by -- --- PROOF ---
  -- the second set is the first's factors and exponents with its own generators
  obtain ⟨p₂, h₂, q₂, c₂, G₂, E₂, GI₂, I₂⟩ := B
  simp only at hp hh hE hB
  subst hp
  subst hh
  have hE' := eq_of_heq hE
  subst hE'
  rintro x (hx | hx)
  · -- the first set: the new factor is 1
    obtain ⟨z, hz, e, he, rfl⟩ := hx
    obtain ⟨a, β, ha, hβ, hzeq⟩ := PolyZonotope.mem_nominalSet_iff.mp hz
    obtain ⟨e', he'⟩ := hB
    -- the independent point is the first set's
    have hzi : (fun i => ∑ j, toReal (A.GI j i) * β j) ∈ (PolyZonotope.step_encloseIndep
        (⟨A.q, fun _ => zero, A.GI, Interval.origin n⟩ : Zonotope (Vec 𝕋 n))
        ⟨q₂, fun _ => zero, GI₂, Interval.origin n⟩).toSet :=
      PolyZonotope.aux_indep_outer _ _ (Zonotope.linComb_outer _ _ ⟨_,
        PolyZonotope.aux_ind_mem A.GI hβ, 0, PolyZonotope.aux_zero_mem GI₂, 1,
        ⟨zero_le_one, le_rfl⟩, by simp⟩)
    have hee : e ∈ (A.I_error.linComb I₂).toSet :=
      Interval.linComb_outer _ _ ⟨e, he, e', he', 1, ⟨zero_le_one, le_rfl⟩, by simp⟩
    -- assemble the point of the enclosure at `σ = 1`
    have := PolyZonotope.aux_assemble A ⟨A.p, A.h, q₂, c₂, G₂, A.E, GI₂, I₂⟩ rfl ha
      (σ := 1) (by simp) hzi hee (z0 := fun i => toReal (A.c i)
        + ∑ l, toReal (A.G l i) * Real.PolyZonotope.monomial A.E a l) (fun i => by
          simp only [Fin.cast_eq_self]
          have hs : ∀ l : Fin A.h, ((toReal (A.G l i) + toReal (G₂ l i)) / 2
              + 1 * ((toReal (A.G l i) - toReal (G₂ l i)) / 2))
              * Real.PolyZonotope.monomial A.E a l
              = toReal (A.G l i) * Real.PolyZonotope.monomial A.E a l := fun l => by ring
          rw [Finset.sum_congr rfl fun l _ => hs l]
          ring)
    convert this using 1
    funext i
    simp only [Pi.add_apply]
    rw [hzeq i]
  · -- the second set: the new factor is -1
    obtain ⟨z, hz, e, he, rfl⟩ := hx
    obtain ⟨a, β, ha, hβ, hzeq⟩ := PolyZonotope.mem_nominalSet_iff.mp hz
    obtain ⟨e', he'⟩ := hA
    -- the independent point is the second set's
    have hzi : (fun i => ∑ j, toReal (GI₂ j i) * β j) ∈ (PolyZonotope.step_encloseIndep
        (⟨A.q, fun _ => zero, A.GI, Interval.origin n⟩ : Zonotope (Vec 𝕋 n))
        ⟨q₂, fun _ => zero, GI₂, Interval.origin n⟩).toSet :=
      PolyZonotope.aux_indep_outer _ _ (Zonotope.linComb_outer _ _ ⟨0,
        PolyZonotope.aux_zero_mem A.GI, _, PolyZonotope.aux_ind_mem GI₂ hβ, 0,
        ⟨le_rfl, zero_le_one⟩, by simp⟩)
    have hee : e ∈ (A.I_error.linComb I₂).toSet :=
      Interval.linComb_outer _ _ ⟨e', he', e, he, 0, ⟨le_rfl, zero_le_one⟩, by simp⟩
    -- assemble the point of the enclosure at `σ = -1`
    have := PolyZonotope.aux_assemble A ⟨A.p, A.h, q₂, c₂, G₂, A.E, GI₂, I₂⟩ rfl ha
      (σ := -1) (by simp) hzi hee (z0 := fun i => toReal (c₂ i)
        + ∑ l, toReal (G₂ l i) * Real.PolyZonotope.monomial A.E a l) (fun i => by
          simp only [Fin.cast_eq_self]
          have hs : ∀ l : Fin A.h, ((toReal (A.G l i) + toReal (G₂ l i)) / 2
              + -1 * ((toReal (A.G l i) - toReal (G₂ l i)) / 2))
              * Real.PolyZonotope.monomial A.E a l
              = toReal (G₂ l i) * Real.PolyZonotope.monomial A.E a l := fun l => by ring
          rw [Finset.sum_congr rfl fun l _ => hs l]
          ring)
    convert this using 1
    funext i
    simp only [Pi.add_apply]
    rw [hzeq i]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
