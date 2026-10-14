module

public import CORALean.ContSet.PolyZonotope.Float.Operations.Subs
public import CORALean.ContSet.PolyZonotope.Float.Theorems.SubsTermsRel
public import CORALean.ContSet.PolyZonotope.Float.Theorems.SubsGClose
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorErrorMonomial
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.PolyZonotope.Real.Operations.Subs

@[expose] public section

/-!
# `PolyZonotope.subs` over-approximates the exact substitution

A point of the exact layer's `subs` of the stored sets, plus a point of the first set's error box,
is a point of the float `subs`. The float terms bracket the exact ones (`subsTerms_rel`), so the
same factor values reach the stored generators, which differ from the exact ones by at most
`subsGDiff` entrywise (`subsG_close`), and that difference, scaled by monomials in `[-1, 1]`, lies
in the box `generatorError` that was added. The substituted set `pZin` is taken as its stored
nominal polynomial: its independent generators and error box are not modelled, as in the exact
layer.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.subs_outer (pZ : PolyZonotope (Vec 𝕋 n)) {nu : ℕ}
    (pZin : PolyZonotope (Vec 𝕋 nu))
    (idu : Fin nu → Fin pZ.p) (share : Fin pZin.p → Option (Fin pZ.p)) :
    (Real.PolyZonotope.subs (nominal pZ) (nominal pZin) idu share).construct
        + pZ.I_error.construct ⊆ (pZ.subs pZin idu share).construct := by -- --- PROOF ---
  rintro _ ⟨z, hz, e, he, rfl⟩
  obtain ⟨a, β, ha, hβ, hz⟩ := Real.PolyZonotope.mem_construct_iff.mp hz
  obtain ⟨hlen, hget⟩ := List.forall₂_iff_get.mp (PolyZonotope.subsTerms_rel pZ pZin idu)
  -- the exact term matching each stored one: same generator, same exponents, bracketed coefficient
  set ρ : Fin (pZ.subsTerms pZin idu).length → ℝ := fun l =>
    ((Real.PolyZonotope.subsTerms (nominal pZ) (nominal pZin) idu).get (Fin.cast hlen l)).2.1
    with hρdef
  have hm : ∀ l : Fin (pZ.subsTerms pZin idu).length,
      ((pZ.subsTerms pZin idu).get l).1 = ((Real.PolyZonotope.subsTerms (nominal pZ)
        (nominal pZin) idu).get (Fin.cast hlen l)).1 ∧
      ((pZ.subsTerms pZin idu).get l).2.2 = ((Real.PolyZonotope.subsTerms (nominal pZ)
        (nominal pZin) idu).get (Fin.cast hlen l)).2.2 ∧
      toReal ((pZ.subsTerms pZin idu).get l).2.1.1 ≤ ρ l ∧
      ρ l ≤ toReal ((pZ.subsTerms pZin idu).get l).2.1.2 :=
    fun l => hget l.1 l.2 (lt_of_lt_of_eq l.2 hlen)
  have hE : ∀ r l, (pZ.subs pZin idu share).E r l
      = (Real.PolyZonotope.subs (nominal pZ) (nominal pZin) idu share).E r (Fin.cast hlen l) := by
    intro r l
    -- same generator and same exponent vector, and the shared-factor map is the exact layer's
    have h1 := (hm l).1
    have h2 := (hm l).2.1
    show (Fin.addCases (motive := fun _ => ℕ) _ _ r) + _
      = (Fin.addCases (motive := fun _ => ℕ) _ _ r) + _
    rw [h1, h2]
    have hf : ∀ j, pZ.subsFactor pZin share j
        = Real.PolyZonotope.subsFactor (nominal pZ) (nominal pZin) share j := fun j => by
      unfold PolyZonotope.subsFactor Real.PolyZonotope.subsFactor
      cases share j <;> rfl
    simp only [hf]
    rfl
  have hmon : ∀ l, Real.PolyZonotope.monomial (pZ.subs pZin idu share).E a l
      = Real.PolyZonotope.monomial
        (Real.PolyZonotope.subs (nominal pZ) (nominal pZin) idu share).E a (Fin.cast hlen l) :=
    fun l => by simp only [Real.PolyZonotope.monomial, hE]; rfl
  -- the shortfall of each stored generator against the exact one
  set Δ : Fin n → Fin (pZ.subsTerms pZin idu).length → ℝ := fun i l =>
    ρ l * toReal (pZ.G ((pZ.subsTerms pZin idu).get l).1 i) - toReal (pZ.subsGDown pZin idu i l)
    with hΔ
  have hbox : (fun i => ∑ l, Δ i l * Real.PolyZonotope.monomial (pZ.subs pZin idu share).E a l)
      ∈ (PolyZonotope.generatorError (pZ.subsGDiff pZin idu)).construct :=
    PolyZonotope.mem_generatorError_monomial (fun i l =>
      PolyZonotope.subsG_close pZ pZin idu l i (hm l).2.2.1 (hm l).2.2.2) ha
  -- the exact point's generator sum, over the stored terms
  have hsum : ∀ i, ∑ l' : Fin (Real.PolyZonotope.subs (nominal pZ) (nominal pZin) idu share).h,
      (Real.PolyZonotope.subs (nominal pZ) (nominal pZin) idu share).G l' i
        * Real.PolyZonotope.monomial
          (Real.PolyZonotope.subs (nominal pZ) (nominal pZin) idu share).E a l'
      = ∑ l : Fin (pZ.subsTerms pZin idu).length,
        ρ l * toReal (pZ.G ((pZ.subsTerms pZin idu).get l).1 i)
          * Real.PolyZonotope.monomial (pZ.subs pZin idu share).E a l := by
    intro i
    -- reindex the exact terms by the stored ones, then compare the term's coefficient
    refine (Fintype.sum_equiv (finCongr hlen) _ _ (fun l => ?_)).symm
    rw [hmon l]
    have h1 := (hm l).1
    have hG : ((Real.PolyZonotope.subs (nominal pZ) (nominal pZin) idu share).G
        (finCongr hlen l)) i = ρ l * toReal (pZ.G ((pZ.subsTerms pZin idu).get l).1 i) := by
      show ((_ : ℝ) • (_ : Vec ℝ n)) i = _
      simp only [Pi.smul_apply, smul_eq_mul, hρdef, h1]
      rfl
    rw [hG]
    rfl
  refine ⟨fun i => toReal ((pZ.subs pZin idu share).c i)
      + (∑ l, toReal (pZ.subsGDown pZin idu i l)
          * Real.PolyZonotope.monomial (pZ.subs pZin idu share).E a l)
      + ∑ j : Fin pZ.q, toReal ((pZ.subs pZin idu share).GI j i) * β j,
    PolyZonotope.mem_nominalSet_iff.mpr ⟨a, β, ha, hβ, fun _ => rfl⟩,
    fun i => (∑ l, Δ i l * Real.PolyZonotope.monomial (pZ.subs pZin idu share).E a l) + e i,
    ?_, ?_⟩
  · -- the sum of the two boxes' points is a point of the interval sum
    intro i
    have h₁ : toReal (pZ.I_error.inf i) ≤ e i := (he i).1
    have h₂ : e i ≤ toReal (pZ.I_error.sup i) := (he i).2
    have h₃ : toReal ((PolyZonotope.generatorError (pZ.subsGDiff pZin idu)).inf i) ≤
          (∑ l, Δ i l * Real.PolyZonotope.monomial (pZ.subs pZin idu share).E a l) ∧
        (∑ l, Δ i l * Real.PolyZonotope.monomial (pZ.subs pZin idu share).E a l) ≤
          toReal ((PolyZonotope.generatorError (pZ.subsGDiff pZin idu)).sup i) := hbox i
    refine ⟨le_trans (addDown_le_add _ _) ?_, le_trans ?_ (add_le_addUp _ _)⟩
    · simp only [Entrywise.entry]
      linarith [h₃.1]
    · simp only [Entrywise.entry]
      linarith [h₃.2]
  · -- the coordinate: the exact point, split into the stored sum and the shortfall
    funext i
    have hzi := hz i
    rw [hsum i] at hzi
    have hs : (∑ l, toReal (pZ.subsGDown pZin idu i l)
          * Real.PolyZonotope.monomial (pZ.subs pZin idu share).E a l)
        + (∑ l, Δ i l * Real.PolyZonotope.monomial (pZ.subs pZin idu share).E a l)
        = ∑ l, ρ l * toReal (pZ.G ((pZ.subsTerms pZin idu).get l).1 i)
          * Real.PolyZonotope.monomial (pZ.subs pZin idu share).E a l := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun l _ => by simp only [hΔ]; ring
    show toReal (pZ.c i) + _ + _ + _ = z i + e i
    rw [hzi]
    show toReal (pZ.c i) + _ + _ + _ = toReal (pZ.c i) + _ + _ + e i
    have hGI : ∑ j, ((nominal pZ).subs (nominal pZin) idu share).GI j i * β j
        = ∑ j : Fin pZ.q, toReal ((pZ.subs pZin idu share).GI j i) * β j := rfl
    beta_reduce
    rw [hGI, ← hs]
    ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
