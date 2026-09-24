import CORALean.NN.Layers.Definitions.ActivationPolyRefinable
import CORALean.NN.Layers.Definitions.PolyFamily
import CORALean.NN.Operations.Convergent
import CORALean.NN.Layers.Theorems.PadToError
import CORALean.NN.Layers.Theorems.Real.ActivationPolySubsetInflate
import CORALean.NN.Layers.Theorems.Real.PolyRelaxationFamilyErrorLt
import CORALean.NN.Layers.Theorems.Real.PolyRelaxationFamilySound

/-!
# Refinement converges at the exact polynomial activation layer

ℝ-only, the enclosure approaching the exact image only at the exact representation. A level per
neuron covering that neuron's own box and leaving `2 · error` under `ε`: nothing waits for the
widest box in the layer, and padding leaves each neuron's error alone.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The level one neuron needs: past both ends of its own box, and past `2 / ε`. -/
theorem aux_exists_level_one (l u : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ o : ℕ, (-(o : ℝ) ≤ l ∧ u ≤ (o : ℝ)) ∧ 2 * (1 / ((o : ℝ) + 1)) ≤ ε := by -- --- PROOF ---
  obtain ⟨M, hM⟩ := exists_nat_gt (2 / ε)
  -- one level past `M` and past both ceilings serves this neuron
  obtain ⟨o, hMo, hlo, huo⟩ : ∃ o : ℕ, M ≤ o ∧ ⌈|l|⌉₊ ≤ o ∧ ⌈|u|⌉₊ ≤ o :=
    ⟨max M (max ⌈|l|⌉₊ ⌈|u|⌉₊), le_max_left _ _,
      le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans (le_max_right _ _) (le_max_right _ _)⟩
  have hl : |l| ≤ (o : ℝ) := le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hlo)
  have hu : |u| ≤ (o : ℝ) := le_trans (Nat.le_ceil _) (Nat.cast_le.mpr huo)
  have hMr : (M : ℝ) ≤ (o : ℝ) := Nat.cast_le.mpr hMo
  have hopos : (0 : ℝ) < (o : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) o]
  refine ⟨o, ⟨by linarith [neg_abs_le l], by linarith [le_abs_self u]⟩, ?_⟩
  -- the level is past `M`, which was chosen past `2 / ε`
  have h2 : 2 / ε < (o : ℝ) + 1 := by linarith
  rw [div_lt_iff₀ hε] at h2
  rw [mul_one_div, div_le_iff₀ hopos]
  linarith

/-- A level per neuron, each covering that neuron's own box and leaving `2 · error` under `ε`. -/
theorem aux_exists_level (s : PolyZonotope (Vec ℝ n)) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : OrderPattern n, ∀ i,
      (-((t i : ℕ) : ℝ) ≤ s.interval.inf i ∧ s.interval.sup i ≤ ((t i : ℕ) : ℝ))
        ∧ 2 * (1 / (((t i : ℕ) : ℝ) + 1)) ≤ ε :=
  ⟨fun i => (aux_exists_level_one (s.interval.inf i) (s.interval.sup i) hε).choose,
    fun i => (aux_exists_level_one (s.interval.inf i) (s.interval.sup i) hε).choose_spec⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- Raising the pattern puts the enclosed set inside any inflation of the exact image. -/
theorem Layer.activationPolyRefinable_convergent {σ σ' : ℝ → ℝ} {Mσ : ℝ}
    (hd : ∀ x, HasDerivAt σ (σ' x) x) (hσ : ∀ x, |σ' x| ≤ Mσ) :
    (Layer.activationPolyRefinable (n := n) (polyRelaxationFamily hd hσ)
      (polyRelaxationFamily_sound hd hσ)).Convergent := by -- --- PROOF ---
  intro s ε hε
  obtain ⟨t, ht⟩ := aux_exists_level s hε
  refine ⟨t, Layer.activationPoly_subset_inflate
    ((polyRelaxationFamily hd hσ).atPattern_sound (polyRelaxationFamily_sound hd hσ) t)
    s hε.le fun i => ?_⟩
  -- padding leaves the error alone, so the neuron's own level is what counts
  have hpad : ((polyRelaxationFamily hd hσ).atPattern t i).error
      = ((polyRelaxationFamily hd hσ).rel (t i)).error := rfl
  rw [hpad]
  have herr := polyRelaxationFamily_error_lt hd hσ (t i) (ht i).1.1
    (s.interval_inf_le_sup i) (ht i).1.2
  linarith [(ht i).2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
