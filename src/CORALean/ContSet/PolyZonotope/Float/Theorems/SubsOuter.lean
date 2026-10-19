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
`aux_subsGDiff` entrywise (`subsG_close`), and that difference, scaled by monomials in `[-1, 1]`,
lies in the box `generatorError` that was added. The substituted set `pZin` is taken as its stored
nominal polynomial: its independent generators and error box are not modelled, as in the exact
layer.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   14-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.subs_outer (pZ : PolyZonotope (Vec 𝕋 n)) {nu : ℕ}
    (pZin : PolyZonotope (Vec 𝕋 nu))
    (idu : Fin nu → Fin pZ.p) (share : Fin pZin.p → Option (Fin pZ.p)) : -- --- STMT ---
    (Real.PolyZonotope.subs (nominal pZ) (nominal pZin) idu share).construct
        + pZ.I_error.construct ⊆ (pZ.subs pZin idu share).construct := by -- --- PROOF ---
  rintro _ ⟨z, hz, e, he, rfl⟩
  -- the exact substituted set
  set R := Real.PolyZonotope.subs (nominal pZ) (nominal pZin) idu share with hR
  obtain ⟨a, β, ha, hβ, hz⟩ := Real.PolyZonotope.mem_construct_iff.mp hz
  obtain ⟨hlen, hget⟩ := List.forall₂_iff_get.mp (PolyZonotope.subsTerms_rel pZ pZin idu)
  -- the two term lists, exact and stored, and the stored monomials
  set mon := Real.PolyZonotope.monomial (pZ.subs pZin idu share).E a with hmon_def
  set rt := Real.PolyZonotope.subsTerms (nominal pZ) (nominal pZin) idu with hrt
  set st := pZ.subsTerms pZin idu with hst
  -- the exact term matching each stored one: same generator, same exponents, bracketed coefficient
  set ρ : Fin st.length → ℝ := fun l => (rt.get (Fin.cast hlen l)).2.1 with hρdef
  have hm : ∀ l : Fin st.length,
      (st.get l).1 = (rt.get (Fin.cast hlen l)).1 ∧
      (st.get l).2.2 = (rt.get (Fin.cast hlen l)).2.2 ∧
      toReal (st.get l).2.1.inf ≤ ρ l ∧
      ρ l ≤ toReal (st.get l).2.1.sup :=
    fun l => hget l.1 l.2 (lt_of_lt_of_eq l.2 hlen)
  have hE : ∀ r l, (pZ.subs pZin idu share).E r l = R.E r (Fin.cast hlen l) := by
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
  have hmon : ∀ l, mon l = Real.PolyZonotope.monomial R.E a (Fin.cast hlen l) :=
    fun l => by simp only [hmon_def, Real.PolyZonotope.monomial, hE]; rfl
  -- the shortfall of each stored generator against the exact one
  set Δ : Fin n → Fin st.length → ℝ := fun i l =>
    ρ l * toReal (pZ.G (st.get l).1 i) - toReal (pZ.aux_subsGDown pZin idu i l)
    with hΔ
  have hbox : (fun i => ∑ l, Δ i l * mon l)
      ∈ (PolyZonotope.generatorError (pZ.aux_subsGDiff pZin idu)).construct :=
    PolyZonotope.mem_generatorError_monomial (fun i l =>
      PolyZonotope.subsG_close pZ pZin idu l i (hm l).2.2.1 (hm l).2.2.2) ha
  -- the exact point's generator sum, over the stored terms
  have hsum : ∀ i, ∑ l' : Fin R.h, R.G l' i * Real.PolyZonotope.monomial R.E a l'
      = ∑ l : Fin st.length, ρ l * toReal (pZ.G (st.get l).1 i) * mon l := by
    intro i
    -- reindex the exact terms by the stored ones, then compare the term's coefficient
    refine (Fintype.sum_equiv (finCongr hlen) _ _ (fun l => ?_)).symm
    rw [hmon l]
    have h1 := (hm l).1
    have hG : R.G (finCongr hlen l) i = ρ l * toReal (pZ.G (st.get l).1 i) := by
      show ((_ : ℝ) • (_ : Vec ℝ n)) i = _
      simp only [Pi.smul_apply, smul_eq_mul, hρdef, h1]
      rfl
    rw [hG]
    rfl
  refine ⟨fun i => toReal ((pZ.subs pZin idu share).c i)
      + (∑ l, toReal (pZ.aux_subsGDown pZin idu i l)
          * mon l)
      + ∑ j : Fin pZ.q, toReal ((pZ.subs pZin idu share).GI j i) * β j,
    PolyZonotope.mem_nominalSet_iff.mpr ⟨a, β, ha, hβ, fun _ => rfl⟩,
    fun i => (∑ l, Δ i l * mon l) + e i,
    ?_, ?_⟩
  · -- the sum of the two boxes' points is a point of the interval sum
    intro i
    have h₁ : toReal (pZ.I_error.inf i) ≤ e i := (he i).1
    have h₂ : e i ≤ toReal (pZ.I_error.sup i) := (he i).2
    have h₃ : toReal ((PolyZonotope.generatorError (pZ.aux_subsGDiff pZin idu)).inf i) ≤
          (∑ l, Δ i l * mon l) ∧
        (∑ l, Δ i l * mon l) ≤
          toReal ((PolyZonotope.generatorError (pZ.aux_subsGDiff pZin idu)).sup i) := hbox i
    refine ⟨le_trans (addDown_le_add _ _) ?_, le_trans ?_ (add_le_addUp _ _)⟩
    · simp only [Entrywise.entry]
      linarith [h₃.1]
    · simp only [Entrywise.entry]
      linarith [h₃.2]
  · -- the coordinate: the exact point, split into the stored sum and the shortfall
    funext i
    have hzi := hz i
    rw [hsum i] at hzi
    have hs : (∑ l, toReal (pZ.aux_subsGDown pZin idu i l)
          * mon l)
        + (∑ l, Δ i l * mon l)
        = ∑ l, ρ l * toReal (pZ.G (st.get l).1 i)
          * mon l := by
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
