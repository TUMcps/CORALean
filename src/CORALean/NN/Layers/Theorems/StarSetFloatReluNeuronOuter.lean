module

public import CORALean.NN.Layers.Operations.StarSetFloatReluNeuron
public import CORALean.ContSet.StarSet.Float.Theorems.MemNominalSet
public import CORALean.NN.Layers.Theorems.StarSetFloatChordRowHolds
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# One ReLU neuron on a float star set encloses the ReLU

If the bounds hold on the star set, the image of the set under the ReLU at the neuron `j` lies
in the set the step returns, as in `Real.StarSet.reluNeuron_outer`, with the stored numbers read as
reals. The bounds are required of the nominal part, as `StarSet.rowBounds` gives them, and the
error box is carried by the step: the ReLU being `1`-Lipschitz, the error at neuron `j` moves the
image of the point by at most its own size, which `StarSet.reluError` makes room for. The
branches are taken on `le`, which certifies `≤` only, so the last branch is sound without knowing
the bounds straddle `0`.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       12-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open ContSet Float.FloatOps Float.SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The nominal part: a point of the nominal star set has the ReLU of neuron `j` in the nominal
star set of the result. -/
theorem StarSet.aux_reluNeuron_nominal (s : StarSet 𝕋 n) (j : Fin n) (b : Interval 𝕋)
    (hb : ∀ x ∈ nominalSet s, toReal b.inf ≤ x j ∧ x j ≤ toReal b.sup) (x : Vec ℝ n)
    (hx : x ∈ nominalSet s) :
    (Function.update x j (max (x j) 0) : Vec ℝ n) ∈
      nominalSet (s.reluNeuron j b) := by -- --- PROOF ---
  have hbx := hb x hx
  rw [StarSet.mem_nominalSet_iff] at hx
  obtain ⟨α, ⟨hα, hcα⟩, hxα⟩ := hx
  unfold StarSet.reluNeuron
  dsimp only
    -- the neuron is nonnegative everywhere: the ReLU is the identity
  by_cases h0 : le zero b.inf = true
  · rw [if_pos h0, StarSet.mem_nominalSet_iff]
    have h0' := toReal_le_of_le h0
    rw [toReal_zero] at h0'
    have : max (x j) 0 = x j := max_eq_left (by linarith [hbx.1])
    rw [this, Function.update_eq_self]
    exact ⟨α, ⟨hα, hcα⟩, hxα⟩
  rw [if_neg h0]
  -- the neuron is nonpositive everywhere: the ReLU is `0`, the row cleared
  by_cases h1 : le b.sup zero = true
  · rw [if_pos h1, StarSet.mem_nominalSet_iff]
    have h1' := toReal_le_of_le h1
    rw [toReal_zero] at h1'
    have : max (x j) 0 = 0 := max_eq_right (by linarith [hbx.2])
    rw [this]
    refine ⟨α, ⟨hα, hcα⟩, fun i => ?_⟩
    by_cases hi : i = j
    · subst hi; simp [toReal_zero]
    · simp [Function.update_of_ne hi, hxα i]
  rw [if_neg h1, StarSet.mem_nominalSet_iff]
  -- the new factor is the value of the ReLU
  have hxj := hxα j
  set β := max (x j) 0 with hβ
  have hβ0 : 0 ≤ β := le_max_right _ _
  have hβx : x j ≤ β := le_max_left _ _
  have hS : ∑ k, toReal (s.G j k) * α k = x j - toReal (s.c j) := by rw [hxj]; ring
  refine ⟨Fin.snoc (α := fun _ => ℝ) α β, ⟨?_, ?_⟩, fun i => ?_⟩
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


-- =======================================  MAIN THEOREM  ======================================= --

theorem StarSet.reluNeuron_outer (s : StarSet 𝕋 n) (j : Fin n) (b : Interval 𝕋)
    (hb : ∀ x ∈ nominalSet s, toReal b.inf ≤ x j ∧ x j ≤ toReal b.sup) :
    (fun (x : Vec ℝ n) => (Function.update x j (max (x j) 0) : Vec ℝ n)) '' s.construct
      ⊆ (s.reluNeuron j b).construct := by -- --- PROOF ---
  rintro _ ⟨_, ⟨x, hx, e, he, rfl⟩, rfl⟩
  -- the nominal point moves as the step says; the error at `j` changes by at most its size
  have hnom := StarSet.aux_reluNeuron_nominal s j b hb x hx
  refine ⟨_, hnom, Function.update e j
    (max (x j + e j) 0 - max (x j) 0), fun i => ?_, ?_⟩
  · have hI : (s.reluNeuron j b).I_error = StarSet.reluError s.I_error j := by
      unfold StarSet.reluNeuron
      dsimp only
      split_ifs <;> rfl
    have he' : toReal (s.I_error.inf i) ≤ e i ∧ e i ≤ toReal (s.I_error.sup i) := he i
    show toReal (((s.reluNeuron j b).I_error).inf i) ≤
        (Function.update e j (max (x j + e j) 0 - max (x j) 0) : Vec ℝ n) i ∧
      (Function.update e j (max (x j + e j) 0 - max (x j) 0) : Vec ℝ n) i ≤
        toReal (((s.reluNeuron j b).I_error).sup i)
    rw [hI]
    unfold StarSet.reluError
    dsimp only
    by_cases hi : i = j
    · subst hi
      simp only [Function.update_self, toReal_neg, toReal_maximum]
      have h := he'
      -- the ReLU is `1`-Lipschitz, and the error is within the radius of its box
      have h1 : |max (x i + e i) 0 - max (x i) 0| ≤ |e i| :=
        (abs_max_sub_max_le_abs (x i + e i) (x i) 0).trans_eq (by rw [add_sub_cancel_left])
      have h2 : |e i| ≤ max (-toReal (s.I_error.inf i)) (toReal (s.I_error.sup i)) := by
        rw [abs_le]
        exact ⟨by linarith [le_max_left (-toReal (s.I_error.inf i)) (toReal (s.I_error.sup i)),
          h.1], by linarith [le_max_right (-toReal (s.I_error.inf i)) (toReal (s.I_error.sup i)),
          h.2]⟩
      exact abs_le.mp (h1.trans h2)
    · simp only [Function.update_of_ne hi]
      exact he'
  · funext i
    by_cases hi : i = j
    · subst hi
      simp
    · simp [Function.update_of_ne hi]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
