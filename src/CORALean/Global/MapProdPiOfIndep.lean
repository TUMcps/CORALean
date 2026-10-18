module

public import Mathlib.Probability.Independence.Basic

@[expose] public section

/-!
# Independent samples beside a block: the law is a product

A step of [1, Thm. 4]: a random element `Z` and samples `y_j`, `j ∈ ι`, each of law `P` and each
independent of a σ-algebra `m_j` in which `Z` and the other samples are measurable, have the joint
law `law(Z) ⊗ Pⁱ`. On a rectangle `a × ∏_j s_j` the measure of `{Z ∈ a} ∩ ⋂_j {y_j ∈ s_j}` splits
off one sample at a time; rectangles of a measurable set and a box generate the product
σ-algebra (`Measure.prod_eq_generateFrom`).
## References

* [1] M. C. Campi, G. Calafiore and S. Garatti. "Interval predictor models: Identification and
      reliability". Automatica, 45(2):382-392, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open MeasureTheory ProbabilityTheory MeasurableSpace


-- =======================================  MAIN THEOREM  ======================================= --

theorem map_prod_pi_eq_of_indep {Ω β Δ ι : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace β]
    [mΔ : MeasurableSpace Δ] [Fintype ι] [DecidableEq ι] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (P : Measure Δ) [IsProbabilityMeasure P] {Z : Ω → β} (hZ : Measurable Z) {y : ι → Ω → Δ}
    (hy : ∀ j, Measurable (y j)) (hyP : ∀ j, μ.map (y j) = P) (m : ι → MeasurableSpace Ω)
    (hZm : ∀ j, Measurable[m j] Z) (hym : ∀ j j', j' ≠ j → Measurable[m j] (y j'))
    (hind : ∀ j, Indep (MeasurableSpace.comap (y j) mΔ) (m j) μ) : -- --- STMT ---
    μ.map (fun ω => (Z ω, fun j => y j ω)) =
      (μ.map Z).prod (Measure.pi fun _ : ι => P) := by -- --- PROOF ---
  -- on a rectangle the measure splits off one sample at a time
  have key : ∀ (T : Finset ι) {a : Set β}, MeasurableSet a → ∀ {s : ι → Set Δ},
      (∀ j, MeasurableSet (s j)) →
      μ (Z ⁻¹' a ∩ ⋂ j ∈ T, y j ⁻¹' s j) = μ (Z ⁻¹' a) * ∏ j ∈ T, P (s j) := by
    intro T a ha s hs
    induction T using Finset.induction_on with
    | empty => simp
    | insert j T hj ih =>
      have hE : MeasurableSet[m j] (Z ⁻¹' a ∩ ⋂ j' ∈ T, y j' ⁻¹' s j') := by
        refine (hZm j ha).inter ?_
        refine Finset.measurableSet_biInter T fun j' hj' => hym j j' ?_ (hs j')
        rintro rfl; exact hj hj'
      have h := (Indep_iff _ _ _).mp (hind j) (y j ⁻¹' s j) _ ⟨s j, hs j, rfl⟩ hE
      have hset : Z ⁻¹' a ∩ ⋂ j' ∈ insert j T, y j' ⁻¹' s j' =
          y j ⁻¹' s j ∩ (Z ⁻¹' a ∩ ⋂ j' ∈ T, y j' ⁻¹' s j') := by
        rw [Finset.set_biInter_insert]; ext; simp only [Set.mem_inter_iff]; tauto
      rw [hset, h, ih, Finset.prod_insert hj, ← hyP j, Measure.map_apply (hy j) (hs j)]
      ring
  have hpair : Measurable fun ω => (Z ω, fun j => y j ω) :=
    hZ.prodMk (measurable_pi_lambda _ hy)
  -- the boxes span the product measure
  let hD : (Measure.pi fun _ : ι => P).FiniteSpanningSetsIn
      (Set.pi Set.univ '' Set.pi Set.univ fun _ => {s : Set Δ | MeasurableSet s}) :=
    { set := fun _ => Set.univ
      set_mem := fun _ => ⟨fun _ => Set.univ, fun _ _ => MeasurableSet.univ, Set.pi_univ _⟩
      finite := fun _ => measure_lt_top _ _
      spanning := Set.iUnion_const _ }
  refine (Measure.prod_eq_generateFrom generateFrom_measurableSet generateFrom_pi
    isPiSystem_measurableSet isPiSystem_pi (μ.map Z).toFiniteSpanningSetsIn hD ?_).symm
  rintro a ha _ ⟨s, hs, rfl⟩
  have hs' : ∀ j, MeasurableSet (s j) := fun j => hs j (Set.mem_univ j)
  rw [Measure.map_apply hpair (ha.prod (MeasurableSet.univ_pi hs')), Measure.map_apply hZ ha,
    Measure.pi_pi]
  have hpre : (fun ω => (Z ω, fun j => y j ω)) ⁻¹' (a ×ˢ Set.pi Set.univ s) =
      Z ⁻¹' a ∩ ⋂ j ∈ (Finset.univ : Finset ι), y j ⁻¹' s j := by
    ext ω; simp
  rw [hpre, key Finset.univ ha hs']

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
