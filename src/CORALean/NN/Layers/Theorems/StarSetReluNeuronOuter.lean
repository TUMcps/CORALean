module

public import CORALean.NN.Layers.Definitions.Relu
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import CORALean.NN.Layers.Operations.StarSetReluNeuron
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.IntersectionExact
public import CORALean.ContSet.Interval.Real.Theorems.MemAppendIff
public import CORALean.ContSet.HPolytope.Float.Theorems.MemIneqsIff

@[expose] public section

/-!
# What one ReLU neuron on a star set encloses

Given bounds the neuron's value respects on the set, the ReLU at that neuron maps the set into
the star set the step builds. Where `0 ≤ l` the neuron is the identity, where `u ≤ 0` it is `0`,
and between, `β = relu (x_j)` is the new factor: it is above `0` and above `x_j`, and under the
chord from `(l, 0)` to `(u, u)`, since `max` is convex.

## Inputs
* `n` – layer width
* `s` – star set
* `j` – neuron index
* `b` – bounds of the neuron

## Hypotheses
* `hb` – the neuron stays within its bounds on the star set

## Conclusion
* the ReLU image of the star set lies in the set after the step
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet


-- =======================================  MAIN THEOREM  ======================================= --

theorem StarSet.reluNeuron_outer {n : ℕ} (s : StarSet ℋ𝒫 n) (j : Fin n)
    (b : Interval ℝ)
    (hb : ∀ x ∈ construct s, b.inf ≤ x j ∧ x j ≤ b.sup) : -- --- CONCL ---
    (fun (x : Vec ℝ n) => (Function.update x j (Real.relu (x j)) : Vec ℝ n)) '' construct s
      ⊆ construct (s.reluNeuron j b) := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩
  beta_reduce
  have hbx := hb x hx
  obtain ⟨α, ⟨hα, hcα⟩, hxα⟩ := hx
  unfold StarSet.reluNeuron
  -- the neuron is nonnegative everywhere: the ReLU is the identity
  by_cases h0 : 0 ≤ b.inf
  · rw [if_pos h0]
    have : Real.relu (x j) = x j := max_eq_left (by linarith [hbx.1])
    rw [this, Function.update_eq_self]
    exact ⟨α, ⟨hα, hcα⟩, hxα⟩
  rw [if_neg h0]
  -- the neuron is nonpositive everywhere: the ReLU is `0`, the row cleared
  by_cases h1 : b.sup ≤ 0
  · rw [if_pos h1]
    have : Real.relu (x j) = 0 := max_eq_right (by linarith [hbx.2])
    rw [this]
    refine ⟨α, ⟨hα, hcα⟩, fun i => ?_⟩
    by_cases hi : i = j
    · subst hi; simp
    · simp [Function.update_of_ne hi, hxα i]
  rw [if_neg h1]
  rw [not_le] at h0
  rw [not_le] at h1
  -- the triangle: the new factor is the value of the ReLU
  set β := Real.relu (x j) with hβ
  have hxj := hxα j
  have hβ0 : 0 ≤ β := le_max_right _ _
  have hβx : x j ≤ β := le_max_left _ _
  have hβu : β ≤ b.sup := max_le hbx.2 h1.le
  -- the chord from `(l, 0)` to `(u, u)` lies above the ReLU
  have hden : 0 < b.sup - b.inf := by linarith
  have hchord : β ≤ b.sup / (b.sup - b.inf) * (x j - b.inf) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hden]
    rcases le_total (x j) 0 with h | h
    · rw [hβ, Real.relu, max_eq_right h]; nlinarith [hbx.1]
    · rw [hβ, Real.relu, max_eq_left h]; nlinarith [hbx.2]
  -- the old factors with `β` appended witness the new set
  have hS : ∑ k, s.G j k * α k = x j - s.c j := by rw [hxj]; ring
  -- a row on the factors with `β` appended, read as the old row and the new coefficient
  have hrow : ∀ (a : Fin s.m → ℝ) (t : ℝ), ∑ k : Fin (s.m + 1),
      Fin.snoc (α := fun _ => ℝ) a t k * Fin.snoc (α := fun _ => ℝ) α β k
        = ∑ k, a k * α k + t * β := fun a t => by
    simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  have hlast : ∀ k : Fin 1, Fin.natAdd s.m k = Fin.last s.m := fun k =>
    Fin.ext (by simp)
  refine ⟨Fin.snoc (α := fun _ => ℝ) α β, ⟨(Interval.mem_append_iff _ _ _).mpr ⟨?_, fun k => ?_⟩,
    (HPolytope.intersection_exact _ _).subset ⟨?_, HPolytope.mem_ineqs_iff.mpr fun r => ?_⟩⟩,
    fun i => ?_⟩
  · -- the old factors in the old box, the new one in `[0, u]`
    have hA : (fun k => (Fin.snoc (α := fun _ => ℝ) α β : Vec ℝ (s.m + 1)) (Fin.castAdd 1 k))
        = α := funext fun k => Fin.snoc_castSucc (α := fun _ => ℝ) _ _ _
    exact (congrArg (· ∈ s.dom.construct) hA).mpr hα
  · show 0 ≤ Fin.snoc (α := fun _ => ℝ) α β (Fin.natAdd s.m k)
      ∧ Fin.snoc (α := fun _ => ℝ) α β (Fin.natAdd s.m k) ≤ b.sup
    rw [hlast k, Fin.snoc_last]
    exact ⟨hβ0, hβu⟩
  · -- the old rows, which read the old factors only
    rw [HPolytope.lift_exact]
    have hA : (fun k => (Fin.snoc (α := fun _ => ℝ) α β : Vec ℝ (s.m + 1)) (Fin.castSucc k))
        = α := funext fun k => Fin.snoc_castSucc (α := fun _ => ℝ) _ _ _
    exact (congrArg (· ∈ s.pred.construct) hA).mpr hcα
  · -- the three new rows
    fin_cases r
    · show ∑ k, Fin.snoc (α := fun _ => ℝ) 0 (-1) k * Fin.snoc (α := fun _ => ℝ) α β k ≤ 0
      rw [hrow]
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]
      linarith
    · show ∑ k, Fin.snoc (α := fun _ => ℝ) (s.G j) (-1) k * Fin.snoc (α := fun _ => ℝ) α β k
        ≤ -s.c j
      rw [hrow, hS]
      linarith
    · show ∑ k, Fin.snoc (α := fun _ => ℝ) (fun k => -(b.sup / (b.sup - b.inf)) * s.G j k) 1 k
          * Fin.snoc (α := fun _ => ℝ) α β k
        ≤ b.sup / (b.sup - b.inf) * (s.c j - b.inf)
      have hS' : ∑ k : Fin s.m, -(b.sup / (b.sup - b.inf)) * s.G j k * α k
          = -(b.sup / (b.sup - b.inf)) * (x j - s.c j) := by
        rw [← hS, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [hrow, hS']
      linarith
  · -- the point: the neuron is `β`, the others are untouched
    by_cases hi : i = j
    · subst hi
      simp [Fin.sum_univ_castSucc]
    · simp [Fin.sum_univ_castSucc, hi, hxα i]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
