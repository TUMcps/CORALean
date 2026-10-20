module

public import Mathlib.Probability.Independence.Basic

@[expose] public section

/-!
# The middle of three blocks is independent of the two outer ones

A step of [1, Thm. 4] under `M`-dependence: if `A` is independent of `(B, C)` and `(A, B)` of
`C`, then `B` is independent of `(A, C)`. For `a ∈ A`, `b ∈ B`, `c ∈ C` the two hypotheses give
`μ(a ∩ b ∩ c) = μ(a)μ(b)μ(c)` and `μ(a ∩ c) = μ(a)μ(c)`, and the sets `a ∩ c` are a π-system
generating `A ⊔ C`. A point of an `M`-dependent sequence is so independent of points more than
`M` away on both sides, though the definition only separates a past from a future.

## Inputs
* `Ω` – sample space
* `mΩ` – its sigma-algebra
* `μ` – probability measure
* `mA` – sigma-algebra of the first block
* `mB` – sigma-algebra of the middle block
* `mC` – sigma-algebra of the last block

## Hypotheses
* `hA` – the first block is measurable
* `hB` – the middle block is measurable
* `hC` – the last block is measurable
* `h1` – the first block is independent of the other two
* `h2` – the first two blocks are independent of the last

## Conclusion
* the middle block is independent of the two outer ones

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

theorem indep_mid_of_indep {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {mA mB mC : MeasurableSpace Ω} (hA : mA ≤ mΩ) (hB : mB ≤ mΩ)
    (hC : mC ≤ mΩ) (h1 : Indep mA (mB ⊔ mC) μ) (h2 : Indep (mA ⊔ mB) mC μ) : -- --- CONCL ---
    Indep mB (mA ⊔ mC) μ := by -- --- PROOF ---
  -- the intersections `a ∩ c` generate `A ⊔ C`
  let p : Set (Set Ω) := {s | ∃ a c, MeasurableSet[mA] a ∧ MeasurableSet[mC] c ∧ s = a ∩ c}
  have hp : IsPiSystem p := by
    rintro _ ⟨a, c, ha, hc, rfl⟩ _ ⟨a', c', ha', hc', rfl⟩ _
    exact ⟨a ∩ a', c ∩ c', ha.inter ha', hc.inter hc', by ext; simp only [Set.mem_inter_iff]; tauto⟩
  have hgen : mA ⊔ mC = generateFrom p := by
    refine le_antisymm (sup_le (fun a ha => measurableSet_generateFrom ⟨a, Set.univ, ha,
      MeasurableSet.univ, by simp⟩) (fun c hc => measurableSet_generateFrom ⟨Set.univ, c,
      MeasurableSet.univ, hc, by simp⟩)) (generateFrom_le ?_)
    rintro _ ⟨a, c, ha, hc, rfl⟩
    exact ((le_sup_left : mA ≤ mA ⊔ mC) a ha).inter ((le_sup_right : mC ≤ mA ⊔ mC) c hc)
  refine IndepSets.indep hB (sup_le hA hC) (@isPiSystem_measurableSet Ω mB) hp
    (@generateFrom_measurableSet Ω mB).symm hgen ?_
  rw [IndepSets_iff]
  rintro b _ hb ⟨a, c, ha, hc, rfl⟩
  rw [Indep_iff] at h1 h2
  -- the product rule for the three, from the two hypotheses
  have e1 : μ (a ∩ b) = μ a * μ b := h1 a b ha ((le_sup_left : mB ≤ mB ⊔ mC) b hb)
  have e2 : μ (a ∩ c) = μ a * μ c := h1 a c ha ((le_sup_right : mC ≤ mB ⊔ mC) c hc)
  have e3 : μ (a ∩ b ∩ c) = μ (a ∩ b) * μ c :=
    h2 _ c (((le_sup_left : mA ≤ mA ⊔ mB) a ha).inter ((le_sup_right : mB ≤ mA ⊔ mB) b hb)) hc
  have hset : b ∩ (a ∩ c) = a ∩ b ∩ c := by ext; simp only [Set.mem_inter_iff]; tauto
  rw [hset, e3, e1, e2]
  ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
