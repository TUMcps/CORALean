module

public import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMapCora
public import CORALean.ContSet.PolyZonotope.Float.Theorems.ConstructOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.FoldConstantsOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.PolyZonotope.Float.Theorems.Basic
public import CORALean.ContSet.Zonotope.Float.Theorems.Basic
public import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne
public import CORALean.ContSet.Conversion.Float.Theorems.PolyZonotopeZonotopeFoldContains
public import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.QuadEntryBracket
public import CORALean.ContSet.Zonotope.Float.Theorems.QuadMapMixedOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.QuadMapTriFilteredOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.QuadMapTriSumSqSplit
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter

@[expose] public section

/-!
# Float `quadMapCora` encloses the quadratic image of a polynomial zonotope

A point is `x = d + r`: `d = c + Σ mₗ(α) gₗ` the dependent part at the factors `α`, a point of
`D` (`construct_outer`, `zonotopeFold_contains`), and `r` the independent part with the error, a
point of `R`. Then `xᵀQx = dᵀQd + (rᵀQr + dᵀQr + rᵀQd)`: the bracket is in the sum of the three
zonotope maps (`quadMapTriFiltered_outer`, `quadMapMixed_outer`, `Zonotope.plus_outer`), and
`dᵀQd = Σ_{j ≤ k} m'ⱼ m'ₖ Pⱼₖ` with `m' = [1 m(α)]` the monomials of `[0 E]`, `Pⱼⱼ = Mⱼⱼ` and
`Pⱼₖ = Mⱼₖ + Mₖⱼ`: the products at the same factors. Their rounding goes to the box;
`construct_outer` and `foldConstants_outer` keep the set.

## Inputs
* `Q` – quadratic form per output coordinate
* `order` – column order of CORA's constructor
* `pZ` – polynomial zonotope

## Hypotheses
* none

## Conclusion
* the quadratic image of `pZ` is contained in the computed polynomial zonotope
-/

-- Authors:       Claude Opus 5.5
-- Written:       20-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix Finset FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The double sum over `N + 1` columns as the sum over the products `j ≤ k`, numbered as
`quadMapCora` numbers them. -/
private theorem PolyZonotope.aux_quadMapCora_pairs (N : ℕ)
    (f : Fin (N + 1) → Fin (N + 1) → ℝ) : -- --- CONCL ---
    ∑ a, ∑ b, f a b = ∑ u : Fin (PolyZonotope.step_quadMapCoraPairs N),
      (let jk := PolyZonotope.step_quadMapCoraPair N u
       if jk.1 = jk.2 then f jk.1 jk.1 else f jk.1 jk.2 + f jk.2 jk.1) := by -- --- PROOF ---
  set F : ℕ → ℕ → ℝ := fun a b => if h : a < N + 1 ∧ b < N + 1 then f ⟨a, h.1⟩ ⟨b, h.2⟩ else 0
    with hF
  have hf : ∀ a b : Fin (N + 1), f a b = F a.val b.val := fun a b => by
    simp only [hF]; rw [dif_pos ⟨a.2, b.2⟩]
  -- the products by the column `j` and the offset `r` of the other column
  set G : ℕ → ℕ → ℝ := fun j r => if r = 0 then F j j else F j (j + r) + F (j + r) j with hG
  have hu : ∀ u : Fin (PolyZonotope.step_quadMapCoraPairs N),
      (let jk := PolyZonotope.step_quadMapCoraPair N u
       if jk.1 = jk.2 then f jk.1 jk.1 else f jk.1 jk.2 + f jk.2 jk.1)
      = (fun σ : Σ j : Fin (N + 1), Fin (N + 1 - j.val) => G σ.1.val σ.2.val)
        (finSigmaFinEquiv.symm u) := fun u => by
    simp only [PolyZonotope.step_quadMapCoraPair, hG, hf, Fin.ext_iff]
    by_cases h0 : (finSigmaFinEquiv.symm u).2.val = 0
    · simp [h0]
    · rw [if_neg (by omega), if_neg h0]
  rw [Finset.sum_congr rfl fun u _ => hu u]
  rw [Equiv.sum_comp finSigmaFinEquiv.symm (fun σ : Σ j : Fin (N + 1), Fin (N + 1 - j.val) =>
    G σ.1.val σ.2.val), Fintype.sum_sigma]
  -- both sides in ranges
  have hl : ∑ a : Fin (N + 1), ∑ b : Fin (N + 1), f a b
      = ∑ a ∈ range (N + 1), ∑ b ∈ range (N + 1), F a b := by
    simp_rw [hf]
    rw [Fin.sum_univ_eq_sum_range (fun a => ∑ b : Fin (N + 1), F a b.val) (N + 1)]
    exact Finset.sum_congr rfl fun a _ => Fin.sum_univ_eq_sum_range (fun b => F a b) (N + 1)
  have hp : ∑ j : Fin (N + 1), ∑ r : Fin (N + 1 - j.val), G j.val r.val
      = ∑ j ∈ range (N + 1), ∑ r ∈ range (N + 1 - j), G j r := by
    rw [Fin.sum_univ_eq_sum_range (fun j => ∑ r ∈ range (N + 1 - j), G j r) (N + 1) |>.symm]
    exact Finset.sum_congr rfl fun j _ =>
      Fin.sum_univ_eq_sum_range (fun r => G j.val r) (N + 1 - j.val)
  rw [hl, hp, Zonotope.quadMapTri_sum_sq_split F N]
  -- each column: the square, then the offsets `t + 1`
  have hcol : ∀ j ∈ range (N + 1), ∑ r ∈ range (N + 1 - j), G j r
      = F j j + ∑ t ∈ range (N - j), (F (j + 1 + t) j + F j (j + 1 + t)) := by
    intro j hj
    have hj' : N + 1 - j = N - j + 1 := by have := Finset.mem_range.mp hj; omega
    rw [hj', Finset.sum_range_succ', add_comm]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [hG, if_neg (Nat.succ_ne_zero t)]
    rw [show j + (t + 1) = j + 1 + t by omega, add_comm]
  rw [Finset.sum_congr rfl hcol, Finset.sum_add_distrib, Finset.sum_range_succ (fun j =>
    ∑ t ∈ range (N - j), (F (j + 1 + t) j + F j (j + 1 + t))) N]
  simp

/-- The monomial of the exponents `[0 E]`: one, then the monomials of `E`. -/
private theorem PolyZonotope.aux_quadMapCora_monomial {p h : ℕ} (E : Fin p → Fin h → ℕ)
    (a : Fin p → ℝ) (j : Fin (h + 1)) :
    Real.PolyZonotope.monomial (fun k => (Fin.cons 0 (E k) : Fin (h + 1) → ℕ)) a j
      = (Fin.cons 1 (Real.PolyZonotope.monomial E a) : Fin (h + 1) → ℝ) j := by
  refine Fin.cases ?_ (fun l => ?_) j
  · simp [Real.PolyZonotope.monomial]
  · simp [Real.PolyZonotope.monomial]

/-- The products of `[c G]` at the factors `α` and the independent part's image `v ∈ IR` lie in
the stored products with `IR` as independent part. -/
private theorem PolyZonotope.aux_quadMapCora_products (Q : Fin m → Mat 𝕋 n n) {p N : ℕ}
    (Zext : Fin (N + 1) → Vec 𝕋 n) (Eext : Fin p → Fin (N + 1) → ℕ) (IR : Zonotope (Vec 𝕋 m))
    {a : Fin p → ℝ} (ha : ∀ k, |a k| ≤ 1) {v : Vec ℝ m} (hv : v ∈ IR.toSet) : -- --- CONCL ---
    (fun i => (∑ j, Real.PolyZonotope.monomial Eext a j • toRealVec (Zext j)) ⬝ᵥ
        (toRealMat (Q i) *ᵥ ∑ j, Real.PolyZonotope.monomial Eext a j • toRealVec (Zext j)) + v i)
      ∈ (PolyZonotope.step_quadMapCoraProducts Q Zext Eext IR).toSet := by -- --- PROOF ---
  obtain ⟨w, hw, eI, heI, rfl⟩ := hv
  obtain ⟨γ, hγ, hwγ⟩ := Zonotope.mem_nominalSet_iff.mp hw
  set S := PolyZonotope.step_quadMapCoraProducts Q Zext Eext IR with hS
  set mon := Real.PolyZonotope.monomial Eext a with hmon
  set pr := PolyZonotope.step_quadMapCoraPair N with hpr
  set B : Fin m → Fin (N + 1) → Fin (N + 1) → ℝ := fun i j k =>
    toRealVec (Zext j) ⬝ᵥ (toRealMat (Q i) *ᵥ toRealVec (Zext k)) with hB
  set P : Fin m → Fin (PolyZonotope.step_quadMapCoraPairs N) → ℝ := fun i u =>
    if (pr u).1 = (pr u).2 then B i (pr u).1 (pr u).1
    else B i (pr u).1 (pr u).2 + B i (pr u).2 (pr u).1 with hP
  -- the monomial of a product is the product of the two monomials
  have hmonS : ∀ u, Real.PolyZonotope.monomial S.E a u = mon (pr u).1 * mon (pr u).2 := by
    intro u
    simp only [Real.PolyZonotope.monomial, hmon, hpr]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← pow_add]
    rfl
  -- the products, bracketed
  have hb : ∀ i u, toReal (PolyZonotope.step_quadMapCoraGDown (Q i) Zext u) ≤ P i u
      ∧ P i u ≤ toReal (PolyZonotope.step_quadMapCoraGUp (Q i) Zext u) := by
    intro i u
    simp only [PolyZonotope.step_quadMapCoraGDown, PolyZonotope.step_quadMapCoraGUp, hP, hB, ← hpr]
    split_ifs
    · exact Zonotope.quadEntry_bracket (Q i) _ _
    · have h1 := Zonotope.quadEntry_bracket (Q i) (Zext (pr u).1) (Zext (pr u).2)
      have h2 := Zonotope.quadEntry_bracket (Q i) (Zext (pr u).2) (Zext (pr u).1)
      have hd := addDown_le_add (Zonotope.quadEntryDown (Q i) (Zext (pr u).1) (Zext (pr u).2))
        (Zonotope.quadEntryDown (Q i) (Zext (pr u).2) (Zext (pr u).1))
      have hu := add_le_addUp (Zonotope.quadEntryUp (Q i) (Zext (pr u).1) (Zext (pr u).2))
        (Zonotope.quadEntryUp (Q i) (Zext (pr u).2) (Zext (pr u).1))
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  -- the coefficients of the products are in `[-1, 1]`
  have hm1 : ∀ u, |Real.PolyZonotope.monomial S.E a u| ≤ 1 := fun u =>
    Real.PolyZonotope.abs_monomial_le_one S.E ha u
  -- the rounding of the products, in the box
  have heP : (fun i => ∑ u, (P i u - toReal (S.G u i)) * Real.PolyZonotope.monomial S.E a u)
      ∈ (Zonotope.generatorError fun i u =>
        subUp (PolyZonotope.step_quadMapCoraGUp (Q i) Zext u)
          (PolyZonotope.step_quadMapCoraGDown (Q i) Zext u)).toSet := by
    refine Zonotope.mem_generatorError (fun i u => ?_) hm1
    have hgap := sub_le_subUp (PolyZonotope.step_quadMapCoraGUp (Q i) Zext u)
      (PolyZonotope.step_quadMapCoraGDown (Q i) Zext u)
    show |P i u - toReal (PolyZonotope.step_quadMapCoraGDown (Q i) Zext u)| ≤ _
    rw [abs_of_nonneg (sub_nonneg.2 (hb i u).1)]
    linarith [(hb i u).2]
  -- the point: the same factors, `IR`'s coefficients, the two boxes added
  refine ⟨_, PolyZonotope.mem_nominalSet_iff.mpr ⟨a, γ, ha, hγ, fun _ => rfl⟩, _,
    Interval.plus_outer _ _ ⟨eI, heI, _, heP, rfl⟩, ?_⟩
  funext i
  -- the dependent form as the sum over the products
  have hexp : (∑ j, mon j • toRealVec (Zext j)) ⬝ᵥ (toRealMat (Q i) *ᵥ ∑ j, mon j •
      toRealVec (Zext j)) = ∑ u, Real.PolyZonotope.monomial S.E a u * P i u := by
    have h2 : (∑ j, mon j • toRealVec (Zext j)) ⬝ᵥ (toRealMat (Q i) *ᵥ ∑ k, mon k •
        toRealVec (Zext k)) = ∑ j, ∑ k, (mon j * mon k) * B i j k := by
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, sum_dotProduct,
        smul_dotProduct, dotProduct_smul, smul_eq_mul, hB]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    -- the pairs `j ≤ k`, each the product of its two monomials
    rw [h2, PolyZonotope.aux_quadMapCora_pairs]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [hmonS u]
    simp only [hP, ← hpr]
    split_ifs with h
    · rw [← h]
    · ring
  show toReal (S.c i) + (∑ u, toReal (S.G u i) * Real.PolyZonotope.monomial S.E a u)
      + ∑ j, toReal (S.GI j i) * γ j
      + (eI i + ∑ u, (P i u - toReal (S.G u i)) * Real.PolyZonotope.monomial S.E a u)
      = _ + (w i + eI i)
  rw [hexp]
  -- the stored products plus their rounding are the exact ones
  have hsum : ∑ u, toReal (S.G u i) * Real.PolyZonotope.monomial S.E a u
      + ∑ u, (P i u - toReal (S.G u i)) * Real.PolyZonotope.monomial S.E a u
      = ∑ u, Real.PolyZonotope.monomial S.E a u * P i u := by
    refine Finset.sum_add_distrib.symm.trans (Finset.sum_congr rfl fun u _ => ?_)
    ring
  have hwi := hwγ i
  show toReal (IR.c i) + _ + ∑ j, toReal (IR.G j i) * γ j + _ = _
  linarith [hsum, hwi]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `{xᵀQ⁽ⁱ⁾x | x ∈ pZ} ⊆ pZ.quadMapCora Q order`. -/
theorem PolyZonotope.quadMapCora_outer (Q : Fin m → Mat 𝕋 n n)
    (order : ℕ → Array (Array ℕ) → Array ℕ) (pZ : PolyZonotope (Vec 𝕋 n)) : -- --- CONCL ---
    Real.PolyZonotope.quadEval (fun k => toRealMat (Q k)) '' pZ.toSet
      ⊆ (pZ.quadMapCora Q order).toSet := by -- --- PROOF ---
  rintro _ ⟨_, ⟨z, hz, e, he, rfl⟩, rfl⟩
  obtain ⟨a, β, ha, hβ, hz⟩ := PolyZonotope.mem_nominalSet_iff.mp hz
  -- the independent part with the error, a point of `R = (0, GI)` with the box
  set r : Vec ℝ n := fun i => ∑ j, toReal (pZ.GI j i) * β j + e i with hr
  have hrR : ∀ c₀ : Vec 𝕋 n, (∀ i, toReal (c₀ i) = 0) →
      r ∈ (⟨pZ.q, c₀, pZ.GI, pZ.I_error⟩ : Zonotope (Vec 𝕋 n)).toSet := fun c₀ hc₀ =>
    ⟨_, Zonotope.mem_nominalSet_iff.mpr ⟨β, hβ, fun _ => rfl⟩, e, he, by
      funext i; simp [hr, hc₀ i]⟩
  unfold PolyZonotope.quadMapCora
  split_ifs with h0
  · -- no dependent part: the point is a point of the zonotope `(c, GI)` with the box
    have hG0 : ∀ i, ∑ l, toReal (pZ.G l i) * Real.PolyZonotope.monomial pZ.E a l = 0 := by
      intro i
      have : IsEmpty (Fin pZ.h) := by rw [h0]; infer_instance
      exact Finset.sum_of_isEmpty _
    have hx : z + e ∈ (⟨pZ.q, pZ.c, pZ.GI, pZ.I_error⟩ : Zonotope (Vec 𝕋 n)).toSet :=
      ⟨_, Zonotope.mem_nominalSet_iff.mpr ⟨β, hβ, fun i => by rw [hz i, hG0 i, add_zero]⟩, e,
        he, rfl⟩
    obtain ⟨w, hw, eZ, heZ, hweq⟩ := Zonotope.quadMapTriFiltered_outer Q _ ⟨_, hx, rfl⟩
    obtain ⟨γ, hγ, hwγ⟩ := Zonotope.mem_nominalSet_iff.mp hw
    refine ⟨w, PolyZonotope.mem_nominalSet_iff.mpr ⟨a, γ, ha, hγ, fun i => ?_⟩, eZ, heZ, hweq⟩
    rw [hwγ i]
    simp
  · -- the dependent part `d`, a point of `D`
    simp only [Zonotope.materialise_eq, PolyZonotope.materialise_eq]
    set d : Vec ℝ n := fun i => toReal (pZ.c i)
      + ∑ l, toReal (pZ.G l i) * Real.PolyZonotope.monomial pZ.E a l with hd
    have hdD : d ∈ ((⟨pZ.p, pZ.h, 0, pZ.c, pZ.G, pZ.E, Fin.elim0,
        ⟨fun _ => zero, fun _ => zero⟩⟩ : PolyZonotope (Vec 𝕋 n)).construct
          order).zonotopeFold.toSet := by
      refine PolyZonotope.zonotopeFold_contains _ (PolyZonotope.construct_outer _ order ?_)
      refine ⟨d, PolyZonotope.mem_nominalSet_iff.mpr ⟨a, Fin.elim0, ha, fun j => j.elim0,
        fun i => by simp [hd]⟩, 0, fun i => ⟨le_of_eq toReal_zero, le_of_eq toReal_zero.symm⟩,
        add_zero d⟩
    have hrR' := hrR (fun _ => zero) fun _ => toReal_zero
    -- the image of the independent part and the mixed terms, a point of `IR`
    set R : Zonotope (Vec 𝕋 n) := ⟨pZ.q, fun _ => zero, pZ.GI, pZ.I_error⟩ with hR
    set D := ((⟨pZ.p, pZ.h, 0, pZ.c, pZ.G, pZ.E, Fin.elim0,
        ⟨fun _ => zero, fun _ => zero⟩⟩ : PolyZonotope (Vec 𝕋 n)).construct order).zonotopeFold
      with hD
    set v : Vec ℝ m := fun i => r ⬝ᵥ (toRealMat (Q i) *ᵥ r) + d ⬝ᵥ (toRealMat (Q i) *ᵥ r)
      + r ⬝ᵥ (toRealMat (Q i) *ᵥ d) with hv
    have hvIR : v ∈ (PolyZonotope.step_quadMapCoraIndep Q R D).toSet := by
      unfold PolyZonotope.step_quadMapCoraIndep
      split_ifs with hR0
      · -- no independent generator, no box: `r = 0`
        have hr0 : r = 0 := by
          funext i
          have h1 := toReal_le_of_le (hR0.2 i).1
          have h2 := toReal_le_of_le (hR0.2 i).2
          rw [toReal_zero] at h1 h2
          have hei : e i = 0 := le_antisymm (le_trans (he i).2 h1) (le_trans h2 (he i).1)
          have : IsEmpty (Fin pZ.q) := by rw [show pZ.q = R.h from rfl, hR0.1]; infer_instance
          simp [hr, hei, Finset.sum_of_isEmpty]
        refine ⟨0, Zonotope.mem_nominalSet_iff.mpr ⟨Fin.elim0, fun j => j.elim0, fun i => ?_⟩,
          0, fun i => ⟨le_of_eq toReal_zero, le_of_eq toReal_zero.symm⟩, ?_⟩
        · simp [toReal_zero]
        · funext i; simp [hv, hr0]
      · -- the three zonotope maps, added up
        have hA := Zonotope.quadMapTriFiltered_outer Q R ⟨r, hrR', rfl⟩
        have hB := Zonotope.quadMapMixed_outer Q D R hdD hrR'
        have hC := Zonotope.quadMapMixed_outer Q R D hrR' hdD
        exact Zonotope.plus_outer _ _ (Set.add_mem_add (Zonotope.plus_outer _ _
          (Set.add_mem_add hA hB)) hC)
    -- the point is the products at the same factors plus `v`, through the constructor and fold
    have hprod := PolyZonotope.aux_quadMapCora_products Q (Fin.cons pZ.c pZ.G)
      (fun k => Fin.cons 0 (pZ.E k)) _ ha hvIR
    refine PolyZonotope.foldConstants_outer _ (PolyZonotope.construct_outer _ order ?_)
    convert hprod using 1
    funext i
    have hdsum : (∑ j, Real.PolyZonotope.monomial (fun k => (Fin.cons 0 (pZ.E k) :
        Fin (pZ.h + 1) → ℕ)) a j • toRealVec ((Fin.cons pZ.c pZ.G : Fin (pZ.h + 1) → Vec 𝕋 n) j))
        = d := by
      funext i'
      simp only [PolyZonotope.aux_quadMapCora_monomial, Finset.sum_apply, Fin.sum_univ_succ,
        Fin.cons_zero, Fin.cons_succ, Pi.smul_apply, smul_eq_mul, one_mul, hd, toRealVec]
      congr 1
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [hdsum]
    -- the point splits into `d + r`, and the form into the four parts
    have hx : z + e = d + r := by
      funext i'
      simp only [Pi.add_apply, hz i', hd, hr]
      ring
    show Real.PolyZonotope.quadEval _ (z + e) i = _
    rw [hx]
    simp only [Real.PolyZonotope.quadEval, hv, Matrix.mulVec_add, dotProduct_add,
      add_dotProduct]
    ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
