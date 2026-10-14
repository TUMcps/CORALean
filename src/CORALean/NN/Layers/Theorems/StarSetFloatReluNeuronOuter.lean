module

public import CORALean.NN.Layers.Operations.StarSetFloatReluNeuron
public import CORALean.NN.Layers.Theorems.StarSetFloatChordRowHolds

@[expose] public section

/-!
# One ReLU neuron on a float star set encloses the ReLU

If the bounds hold on the star set, the image of the set under the ReLU at the neuron `j` lies
in the set the step returns, as in `Real.StarSet.reluNeuron_outer`, with the stored numbers read as
reals. The branches are taken on `le`, which certifies `≤` only, so the last branch is sound
without knowing the bounds straddle `0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open ContSet Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem StarSet.reluNeuron_outer (s : StarSet 𝕋 n) (j : Fin n) (b : Interval 𝕋)
    (hb : ∀ x ∈ construct s, toReal b.inf ≤ x j ∧ x j ≤ toReal b.sup) :
    (fun (x : Vec ℝ n) => (Function.update x j (max (x j) 0) : Vec ℝ n)) '' construct s
      ⊆ construct (s.reluNeuron j b) := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩
  beta_reduce
  have hbx := hb x hx
  obtain ⟨α, hα, hcα, hxα⟩ := hx
  unfold StarSet.reluNeuron
  -- the neuron is nonnegative everywhere: the ReLU is the identity
  by_cases h0 : le zero b.inf = true
  · rw [if_pos h0]
    have h0' := toReal_le_of_le h0
    rw [toReal_zero] at h0'
    have : max (x j) 0 = x j := max_eq_left (by linarith [hbx.1])
    rw [this, Function.update_eq_self]
    exact ⟨α, hα, hcα, hxα⟩
  rw [if_neg h0]
  -- the neuron is nonpositive everywhere: the ReLU is `0`, the row cleared
  by_cases h1 : le b.sup zero = true
  · rw [if_pos h1]
    have h1' := toReal_le_of_le h1
    rw [toReal_zero] at h1'
    have : max (x j) 0 = 0 := max_eq_right (by linarith [hbx.2])
    rw [this]
    refine ⟨α, hα, hcα, fun i => ?_⟩
    by_cases hi : i = j
    · subst hi; simp [toReal_zero]
    · simp [Function.update_of_ne hi, hxα i]
  rw [if_neg h1]
  -- the new factor is the value of the ReLU
  have hxj := hxα j
  set β := max (x j) 0 with hβ
  have hβ0 : 0 ≤ β := le_max_right _ _
  have hβx : x j ≤ β := le_max_left _ _
  have hS : ∑ k, toReal (s.G j k) * α k = x j - toReal (s.c j) := by rw [hxj]; ring
  refine ⟨Fin.snoc (α := fun _ => ℝ) α β, ?_, ?_, fun i => ?_⟩
  · intro k
    refine Fin.lastCases ?_ (fun k => ?_) k
    · simp only [Fin.snoc_last, Fin.snoc_last, toReal_zero, toReal_maximum]
      exact ⟨hβ0, max_le_max hbx.2 le_rfl⟩
    · simp only [Fin.snoc_castSucc]
      simpa using hα k
  · -- the old rows, then the new ones
    intro r hr
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (⟨r', hr', rfl⟩ | rfl | rfl) | hc
    · simpa [Fin.sum_univ_castSucc, toReal_zero] using hcα r' hr'
    · simp [Fin.sum_univ_castSucc, hβ0, toReal_zero, toReal_neg, toReal_one]
    · simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, hS, toReal_neg,
        toReal_one]
      linarith
    · split_ifs at hc with hg
      · simp only [List.mem_singleton] at hc
        subst hc
        have := StarSet.chordRow_holds s j b hg α hα (by rw [← hxj]; exact hbx)
        rw [← hxj] at this
        exact this
      · simp at hc
  · -- the point: the neuron is `β`, the others are untouched
    by_cases hi : i = j
    · subst hi
      simp [Fin.sum_univ_castSucc, toReal_zero, toReal_one]
    · simp [Fin.sum_univ_castSucc, hi, hxα i, toReal_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
