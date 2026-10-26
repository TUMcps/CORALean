module

public import CORALean.NN.Operations.InputNeuronOrderFloat
public import CORALean.NN.Operations.InputNeuronOrder
public import CORALean.NN.Theorems.IntervalChainSensitivityFloatOuter

@[expose] public section

/-!
# A float ranking of the input neurons is the real one
If `IntervalChain.getInputNeuronOrder` returns a ranking for a float interval chain standing for a
smooth real one (`IntervalChain.IsSound`), the real `getInputNeuronOrder` of the chain of its layers
at every point of the input box is that ranking. `in-order` and `snake` are index lists, the same
in both. The sensitivity of the real chain lies in the float box (`sensitivity_outer`), so each
neuron's real key lies in its key box; strictly separated boxes decide every comparison of the
stable sort as the real keys do, and a sort whose comparisons agree on its elements returns the
same list.

## Inputs
* `c` – float interval chain
* `r` – real interval chain
* `method` – ranking method
* `X` – box of input points
* `x` – real input point
* `inputSize` – image size, if given

## Hypotheses
* `hc` – the float chain stands for the real chain
* `hs` – the real chain's activations have the stored derivatives
* `hx` – the point lies in the box

## Conclusion
* a ranking the float chain returns is the real ranking
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Sorting a list by two comparisons that agree on its elements gives the same list. -/
private theorem aux_mergeSort_congr {α : Type} (le le' : α → α → Bool) (l : List α)
    (h : ∀ a ∈ l, ∀ b ∈ l, le a b = le' a b) : l.mergeSort le = l.mergeSort le' := by
  simpa using List.map_mergeSort (r := le) (s := le') (f := id) (l := l) h

/-- A ranking the key boxes certify is the stable sort by any keys whose order is that of the sums
the boxes enclose. -/
private theorem aux_rankByKey_eq (key : ℕ → Interval 𝕋) (L : List ℕ) (s g : ℕ → ℝ)
    (hs : ∀ a ∈ L, toReal (key a).inf ≤ s a ∧ s a ≤ toReal (key a).sup)
    (hg : ∀ a ∈ L, ∀ b ∈ L, g a ≤ g b ↔ s a ≤ s b) {L' : List ℕ}
    (h : aux_rankByKey key L = some L') : -- --- CONCL ---
    L' = L.mergeSort fun a b => decide (g a ≤ g b) := by -- --- PROOF ---
  unfold aux_rankByKey at h
  split_ifs at h with hcert
  rw [← Option.some.inj h]
  -- the two comparisons agree on every pair of neurons of the list
  refine aux_mergeSort_congr _ _ L fun a ha b hb => ?_
  by_cases hab : a = b
  · subst hab; simp
  have hc := List.all_eq_true.mp (List.all_eq_true.mp hcert a ha) b hb
  simp only [beq_iff_eq, hab, false_or, Bool.or_eq_true] at hc
  by_cases hle : le (key a).sup (key b).inf = true
  · -- `a`'s box lies below `b`'s: both comparisons say `a` first
    have h1 : s a ≤ s b := le_trans (hs a ha).2 (le_trans (toReal_le_of_le hle) (hs b hb).1)
    simp [hle, (hg a ha b hb).mpr h1]
  · -- `b`'s box lies strictly below `a`'s: both say `b` first
    have hlt := toReal_lt_of_ltStrict (hc.resolve_left hle)
    have h1 : ¬ s a ≤ s b :=
      not_le.mpr (lt_of_le_of_lt (hs b hb).2 (lt_of_lt_of_le hlt (hs a ha).1))
    simp [hab, hle, mt (hg a ha b hb).mp h1]

/-- The real key of neuron `j`: the sum over the outputs of the absolute entries of its column of
the sensitivity, `0` past the input width. -/
private noncomputable def aux_sum (S : Mat ℝ m n) (j : ℕ) : ℝ :=
  if hj : j < n then ∑ i, |S i ⟨j, hj⟩| else 0

/-- A sensitivity in its box has its key in the key box. -/
private theorem aux_sensitivityKey_mem {SB : Interval (Mat 𝕋 m n)} {S : Mat ℝ m n}
    (hS : S ∈ SB.construct) (j : ℕ) : -- --- CONCL ---
    toReal (aux_sensitivityKey SB j).inf ≤ aux_sum S j ∧
      aux_sum S j ≤ toReal (aux_sensitivityKey SB j).sup := by -- --- PROOF ---
  by_cases hj : j < n
  · -- every absolute entry is between the stored bounds of its box
    have hS' := Interval.mem_mat_iff.mp hS
    simp only [aux_sensitivityKey, aux_sum, dif_pos hj]
    refine ⟨le_trans (sumDown_le_sum _) (Finset.sum_le_sum fun i _ => ?_),
      le_trans (Finset.sum_le_sum fun i _ => ?_) (sum_le_sumUp _)⟩
    · have h := hS' i ⟨j, hj⟩
      rw [toReal_maximum, toReal_zero, toReal_maximum, toReal_neg]
      exact max_le (abs_nonneg _) (max_le (le_trans h.1 (le_abs_self _))
        (by linarith [h.2, neg_abs_le (S i ⟨j, hj⟩)]))
    · have h := hS' i ⟨j, hj⟩
      rw [toReal_maximum, toReal_neg]
      have h1 := le_max_left (-toReal (SB.inf i ⟨j, hj⟩)) (toReal (SB.sup i ⟨j, hj⟩))
      have h2 := le_max_right (-toReal (SB.inf i ⟨j, hj⟩)) (toReal (SB.sup i ⟨j, hj⟩))
      exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
  · simp [aux_sensitivityKey, aux_sum, dif_neg hj, toReal_zero]

/-- The channel key box encloses the sum of the neurons' real keys over the channels. -/
private theorem aux_channelKey_mem {key : ℕ → Interval 𝕋} {s : ℕ → ℝ}
    (hk : ∀ j, toReal (key j).inf ≤ s j ∧ s j ≤ toReal (key j).sup) (h w ch p : ℕ) :
    toReal (aux_channelKey key h w ch p).inf ≤ ∑ k ∈ Finset.range ch, s (p + h * w * k) ∧
      ∑ k ∈ Finset.range ch, s (p + h * w * k) ≤ toReal (aux_channelKey key h w ch p).sup := by
  rw [Finset.sum_range (fun k => s (p + h * w * k))]
  exact ⟨le_trans (sumDown_le_sum _) (Finset.sum_le_sum fun k _ => (hk _).1),
    le_trans (Finset.sum_le_sum fun k _ => (hk _).2) (sum_le_sumUp _)⟩

/-- Dividing by one count keeps the order, when the count is positive or both sides are `0`. -/
private theorem aux_scale_iff {u v c : ℝ} (hc : 0 < c ∨ u = 0 ∧ v = 0) :
    u / c ≤ v / c ↔ u ≤ v := by
  rcases hc with hc | ⟨rfl, rfl⟩
  · exact div_le_div_iff_of_pos_right hc
  · simp


-- =======================================  MAIN THEOREM  ======================================= --

theorem IntervalChain.getInputNeuronOrder_eq {c : IntervalChain 𝕋 n m}
    {r : Real.IntervalChain n m} (hc : c.IsSound r) (hs : r.IsSmooth) (method : InputOrderMethod)
    (X : Interval (Vec 𝕋 n)) {x : Vec ℝ n} (hx : x ∈ X.construct)
    (inputSize : Option (ℕ × ℕ × ℕ)) : -- --- CONCL ---
    ∀ L ∈ c.getInputNeuronOrder method X inputSize,
      CORALean.getInputNeuronOrder r.toChain method x inputSize = L := by -- --- PROOF ---
  intro L hL
  replace hL : c.getInputNeuronOrder method X inputSize = some L := hL
  -- the real sensitivity lies in the float box, so each real key lies in its key box
  have hS := IntervalChain.sensitivity_outer hc hs X x hx
  have hk := fun j => aux_sensitivityKey_mem hS j
  -- the real mean divides the key by the number of outputs: the order is the key's
  have hm : ∀ a b : ℕ, aux_sum (r.toChain.sensitivity x) a / (m : ℝ) ≤
      aux_sum (r.toChain.sensitivity x) b / (m : ℝ) ↔
      aux_sum (r.toChain.sensitivity x) a ≤ aux_sum (r.toChain.sensitivity x) b := fun a b =>
    aux_scale_iff (by
      -- with no outputs every key is the empty sum
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0; right; simp [aux_sum]
      · left; exact_mod_cast h0)
  cases method with
  | inOrder =>
    cases inputSize with
    | none => simpa [IntervalChain.getInputNeuronOrder, CORALean.getInputNeuronOrder] using hL
    | some t =>
      obtain ⟨h, w, ch⟩ := t
      simpa [IntervalChain.getInputNeuronOrder, CORALean.getInputNeuronOrder] using hL
  | snake =>
    cases inputSize with
    | none => simpa [IntervalChain.getInputNeuronOrder, CORALean.getInputNeuronOrder] using hL
    | some t =>
      obtain ⟨h, w, ch⟩ := t
      simpa [IntervalChain.getInputNeuronOrder, CORALean.getInputNeuronOrder] using hL
  | sensitivity =>
    -- the real key of neuron `j`, the mean over the outputs of the absolute entries
    have e : ∀ j : ℕ, (if hj : j < n then
        (∑ i, |r.toChain.sensitivity x i ⟨j, hj⟩|) / (m : ℝ) else 0) =
        aux_sum (r.toChain.sensitivity x) j / (m : ℝ) := fun j => by
      by_cases hj : j < n <;> simp [aux_sum, hj]
    cases inputSize with
    | none =>
      -- the ranking of the neurons by their keys
      simp only [IntervalChain.getInputNeuronOrder] at hL
      have h := aux_rankByKey_eq _ _ _ (fun j => aux_sum (r.toChain.sensitivity x) j / (m : ℝ))
        (fun a _ => hk a) (fun a _ b _ => hm a b) hL
      simp only [CORALean.getInputNeuronOrder, e]
      exact h.symm
    | some t =>
      obtain ⟨h, w, ch⟩ := t
      -- the mean over the channels divides by the channel count as well
      simp only [IntervalChain.getInputNeuronOrder] at hL
      have hkc := aux_channelKey_mem hk h w ch
      have hg : ∀ a b : ℕ, (∑ k ∈ Finset.range ch,
          aux_sum (r.toChain.sensitivity x) (a + h * w * k) / (m : ℝ)) / (ch : ℝ) ≤
          (∑ k ∈ Finset.range ch,
          aux_sum (r.toChain.sensitivity x) (b + h * w * k) / (m : ℝ)) / (ch : ℝ) ↔
          ∑ k ∈ Finset.range ch, aux_sum (r.toChain.sensitivity x) (a + h * w * k) ≤
          ∑ k ∈ Finset.range ch, aux_sum (r.toChain.sensitivity x) (b + h * w * k) := by
        intro a b
        rw [← Finset.sum_div, ← Finset.sum_div]
        refine (aux_scale_iff ?_).trans (aux_scale_iff ?_)
        · rcases Nat.eq_zero_or_pos ch with h0 | h0
          · subst h0; right; simp
          · left; exact_mod_cast h0
        · rcases Nat.eq_zero_or_pos m with h0 | h0
          · subst h0; right; simp [aux_sum]
          · left; exact_mod_cast h0
      -- the channel keys' boxes certify the ranking, whose order is that of the real means
      have h' := aux_rankByKey_eq _ _ _ _ (fun a _ => hkc a) (fun a _ b _ => hg a b) hL
      simp only [CORALean.getInputNeuronOrder, e]
      exact h'.symm

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
