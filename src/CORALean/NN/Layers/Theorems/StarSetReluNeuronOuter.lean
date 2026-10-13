import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import CORALean.NN.Layers.Operations.StarSetReluNeuron

/-!
# What one ReLU neuron on a star set encloses

Given bounds the neuron's value respects on the set, the ReLU at that neuron maps the set into
the star set the step builds. Where `0 ≤ l` the neuron is the identity, where `u ≤ 0` it is `0`,
and between, `β = max (x_j) 0` is the new factor: it is above `0` and above `x_j`, and under the
chord from `(l, 0)` to `(u, u)`, since `max` is convex.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet


-- =======================================  MAIN THEOREM  ======================================= --

theorem StarSet.reluNeuron_outer {n : ℕ} (s : StarSet n) (j : Fin n) (b : ℝ × ℝ)
    (hb : ∀ x ∈ construct s, b.1 ≤ x j ∧ x j ≤ b.2) :
    (fun (x : Vec ℝ n) => (Function.update x j (max (x j) 0) : Vec ℝ n)) '' construct s
      ⊆ construct (s.reluNeuron j b) := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩
  beta_reduce
  have hbx := hb x hx
  obtain ⟨α, hα, hcα, hxα⟩ := hx
  unfold StarSet.reluNeuron
  -- the neuron is nonnegative everywhere: the ReLU is the identity
  by_cases h0 : 0 ≤ b.1
  · rw [if_pos h0]
    have : max (x j) 0 = x j := max_eq_left (by linarith [hbx.1])
    rw [this, Function.update_eq_self]
    exact ⟨α, hα, hcα, hxα⟩
  rw [if_neg h0]
  -- the neuron is nonpositive everywhere: the ReLU is `0`, the row cleared
  by_cases h1 : b.2 ≤ 0
  · rw [if_pos h1]
    have : max (x j) 0 = 0 := max_eq_right (by linarith [hbx.2])
    rw [this]
    refine ⟨α, hα, hcα, fun i => ?_⟩
    by_cases hi : i = j
    · subst hi; simp
    · simp [Function.update_of_ne hi, hxα i]
  rw [if_neg h1]
  rw [not_le] at h0
  rw [not_le] at h1
  -- the triangle: the new factor is the value of the ReLU
  set β := max (x j) 0 with hβ
  have hxj := hxα j
  have hβ0 : 0 ≤ β := le_max_right _ _
  have hβx : x j ≤ β := le_max_left _ _
  have hβu : β ≤ b.2 := max_le hbx.2 h1.le
  -- the chord from `(l, 0)` to `(u, u)` lies above the ReLU
  have hden : 0 < b.2 - b.1 := by linarith
  have hchord : β ≤ b.2 / (b.2 - b.1) * (x j - b.1) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hden]
    rcases le_total (x j) 0 with h | h
    · rw [hβ, max_eq_right h]; nlinarith [hbx.1]
    · rw [hβ, max_eq_left h]; nlinarith [hbx.2]
  -- the old factors with `β` appended witness the new set
  have hS : ∑ k, s.G j k * α k = x j - s.c j := by rw [hxj]; ring
  refine ⟨Fin.snoc (α := fun _ => ℝ) α β, ?_, ?_, fun i => ?_⟩
  · intro k
    refine Fin.lastCases ?_ (fun k => ?_) k
    · simp only [Fin.snoc_last]
      exact ⟨hβ0, hβu⟩
    · simp only [Fin.snoc_castSucc]
      exact hα k
  · -- the old rows, then the three new ones
    intro r hr
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with ⟨r', hr', rfl⟩ | rfl | rfl | rfl
    · simpa [Fin.sum_univ_castSucc] using hcα r' hr'
    · simp [Fin.sum_univ_castSucc, hβ0]
    · simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, hS]
      linarith
    · have hS' : ∑ k : Fin s.m, -(b.2 / (b.2 - b.1)) * s.G j k * α k
          = -(b.2 / (b.2 - b.1)) * (x j - s.c j) := by
        rw [← hS, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
      rw [hS']
      linarith
  · -- the point: the neuron is `β`, the others are untouched
    by_cases hi : i = j
    · subst hi
      simp [Fin.sum_univ_castSucc]
    · simp [Fin.sum_univ_castSucc, hi, hxα i]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
