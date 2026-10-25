module

public import CORALean.Global.IndepMidOfIndep
public import Mathlib.MeasureTheory.MeasurableSpace.Pi

@[expose] public section

/-!
# A point of an `M`-dependent sequence is independent of the points more than `M` away

A step of [1, Thm. 4]: `x` is `M`-dependent in the sense of Bosq, which the paper cites, when
finitely many of its values at times `L` are independent of those at times `R` whenever every
time of `R` is more than `M` after every time of `L`. Then `x(j)` is independent of the values
at any finite set `S` of times more than `M` from `j`: split `S` at `j` into `L` and `R`; `x_L` is
independent of `(x(j), x_R)` and `(x_L, x(j))` of `x_R`, so `x(j)` is independent of `(x_L, x_R)`
(`indep_mid_of_indep`), which determines `x_S`.

## Inputs
* `μ` – probability measure
* `x` – sequence of random variables
* `M` – dependence lag
* `j` – time of the point
* `S` – finite set of times

## Hypotheses
* `hx` – every variable is measurable
* `hM` – the sequence is dependent only within the lag
* `hS` – every time of the set is more than the lag from the point

## Conclusion
* the point's variable is independent of the variables at the set's times

## References

* [1] M. C. Campi, G. Calafiore and S. Garatti. "Interval predictor models: Identification and
      reliability". Automatica, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open MeasureTheory ProbabilityTheory

variable {Ω Δ : Type*} [MeasurableSpace Δ]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- the block's σ-algebra is the join of its values'
theorem aux_comap_block_le (x : ℕ → Ω → Δ) (T : Finset ℕ) {m : MeasurableSpace Ω}
    (h : ∀ t ∈ T, MeasurableSpace.comap (x t) inferInstance ≤ m) :
    MeasurableSpace.comap (fun ω (s : T) => x s ω) inferInstance ≤ m := by
  rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  exact iSup_le fun s => by rw [MeasurableSpace.comap_comp]; exact h s s.2

-- a value of the block is measurable in the block's σ-algebra
theorem aux_comap_le_block (x : ℕ → Ω → Δ) (T : Finset ℕ) {t : ℕ} (ht : t ∈ T) :
    MeasurableSpace.comap (x t) inferInstance ≤
      MeasurableSpace.comap (fun ω (s : T) => x s ω) inferInstance := by
  have : x t = (fun f : T → Δ => f ⟨t, ht⟩) ∘ fun ω (s : T) => x s ω := rfl
  rw [this, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le


-- =======================================  MAIN THEOREM  ======================================= --

theorem indep_point_of_mDependent [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {x : ℕ → Ω → Δ} (hx : ∀ t, Measurable (x t)) {M : ℕ}
    (hM : ∀ L R : Finset ℕ, (∀ l ∈ L, ∀ r ∈ R, l + M < r) →
      IndepFun (fun ω (l : L) => x l ω) (fun ω (r : R) => x r ω) μ)
    (j : ℕ) (S : Finset ℕ) (hS : ∀ s ∈ S, s + M < j ∨ j + M < s) : -- --- CONCL ---
    Indep (MeasurableSpace.comap (x j) inferInstance)
      (MeasurableSpace.comap (fun ω (s : S) => x s ω) inferInstance) μ := by -- --- PROOF ---
  classical
  set L := S.filter (· < j)
  set R := S.filter (j < ·)
  have hmL : ∀ l ∈ L, l + M < j := fun l hl => by
    obtain ⟨hlS, hlj⟩ := Finset.mem_filter.mp hl
    rcases hS l hlS with h | h <;> omega
  have hmR : ∀ r ∈ R, j + M < r := fun r hr => by
    obtain ⟨hrS, hjr⟩ := Finset.mem_filter.mp hr
    rcases hS r hrS with h | h <;> omega
  have hblock : ∀ T : Finset ℕ, MeasurableSpace.comap (fun ω (s : T) => x s ω) inferInstance ≤
      ‹MeasurableSpace Ω› := fun T => aux_comap_block_le x T fun t _ => (hx t).comap_le
  -- `x_L` is independent of `(x(j), x_R)`, and `(x_L, x(j))` of `x_R`
  have h1 := (IndepFun_iff_Indep _ _ _).mp (hM L (insert j R) fun l hl r hr => by
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact hmL l hl
    · have := hmL l hl; have := hmR r hr; omega)
  have h2 := (IndepFun_iff_Indep _ _ _).mp (hM (insert j L) R fun l hl r hr => by
    rcases Finset.mem_insert.mp hl with rfl | hl
    · exact hmR r hr
    · have := hmL l hl; have := hmR r hr; omega)
  have hj : ∀ T : Finset ℕ, j ∈ T → MeasurableSpace.comap (x j) inferInstance ≤
      MeasurableSpace.comap (fun ω (s : T) => x s ω) inferInstance := fun T hjT =>
    aux_comap_le_block x T hjT
  have hsub : ∀ {A T : Finset ℕ}, A ⊆ T → MeasurableSpace.comap (fun ω (s : A) => x s ω)
      inferInstance ≤ MeasurableSpace.comap (fun ω (s : T) => x s ω) inferInstance :=
    fun {A T} hAT => aux_comap_block_le x A fun t ht => aux_comap_le_block x T (hAT ht)
  have h1' := indep_of_indep_of_le_right h1
    (sup_le (hj _ (Finset.mem_insert_self _ _)) (hsub (Finset.subset_insert _ _)))
  have h2' := indep_of_indep_of_le_left h2
    (sup_le (hsub (Finset.subset_insert _ _)) (hj _ (Finset.mem_insert_self _ _)))
  have hmid := indep_mid_of_indep (hblock L) (hx j).comap_le (hblock R) h1' h2'
  -- `x_S` is a function of `(x_L, x_R)`
  refine indep_of_indep_of_le_right hmid (aux_comap_block_le x S fun s hs => ?_)
  rcases hS s hs with h | h
  · exact (aux_comap_le_block x L (Finset.mem_filter.mpr ⟨hs, by omega⟩)).trans le_sup_left
  · exact (aux_comap_le_block x R (Finset.mem_filter.mpr ⟨hs, by omega⟩)).trans le_sup_right

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
