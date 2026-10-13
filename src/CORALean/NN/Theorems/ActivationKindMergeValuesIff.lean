module

public import CORALean.NN.Operations.ActivationKindMergeValues
public import CORALean.NN.Definitions.ActivationKindFn
public import CORALean.NN.Layers.Theorems.Real.TanhEqSigmoid
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section

/-!
# The merge values are the finite limits

A real is among an activation's `mergeValues` exactly when the function tends to it at `-∞` or at
`+∞`, so the list is `f([-inf, inf])` less the infinite entries, both directions: nothing finite
is missed and nothing extra is listed.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Filter Topology


-- =======================================  MAIN THEOREM  ======================================= --

/-- `y` is a merge value iff `f` tends to `y` at one end. -/
theorem ActivationKind.mergeValues_iff (k : ActivationKind) (y : ℝ) :
    (∃ z ∈ k.mergeValues, (z : ℝ) = y) ↔
      (Tendsto k.fn atBot (𝓝 y) ∨ Tendsto k.fn atTop (𝓝 y)) := by -- --- PROOF ---
  -- the logistic function's limits, from `exp (-t)`
  have hsTop : Tendsto Real.sigmoid atTop (𝓝 1) := by
    have h : Tendsto (fun t : ℝ => (1 + Real.exp (-t))⁻¹) atTop (𝓝 ((1 + 0)⁻¹)) :=
      ((tendsto_const_nhds.add (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot)).inv₀
        (by norm_num))
    have h2 : Tendsto (fun t : ℝ => (1 + Real.exp (-t))⁻¹) atTop (𝓝 1) := by simpa using h
    exact h2
  have hsBot : Tendsto Real.sigmoid atBot (𝓝 0) := by
    have h : Tendsto (fun t : ℝ => 1 + Real.exp (-t)) atBot atTop :=
      tendsto_atTop_add_const_left _ _ (Real.tendsto_exp_atTop.comp tendsto_neg_atBot_atTop)
    exact h.inv_tendsto_atTop
  -- one case per activation, the limits of each against the uniqueness of limits
  cases k with
  | relu =>
    have hTop : Tendsto Real.relu atTop atTop :=
      tendsto_atTop_mono (fun t => le_max_left t 0) tendsto_id
    have hBot : Tendsto Real.relu atBot (𝓝 0) :=
      tendsto_const_nhds.congr' (by
        filter_upwards [eventually_le_atBot 0] with t ht
        exact (max_eq_right ht).symm)
    -- a listed value is a limit; a limit is a listed value, by uniqueness
    constructor
    · rintro ⟨z, hz, rfl⟩
      simp [ActivationKind.mergeValues] at hz
      subst hz
      exact Or.inl (by simpa [ActivationKind.fn] using hBot)
    · rintro (h | h)
      · exact ⟨0, by simp [ActivationKind.mergeValues], by simpa using tendsto_nhds_unique hBot h⟩
      · exact absurd h (not_tendsto_nhds_of_tendsto_atTop hTop y)
  | sigmoid =>
    -- the limits are `0` and `1`
    constructor
    · rintro ⟨z, hz, rfl⟩
      simp [ActivationKind.mergeValues] at hz
      rcases hz with rfl | rfl
      · exact Or.inl (by simpa [ActivationKind.fn] using hsBot)
      · exact Or.inr (by simpa [ActivationKind.fn] using hsTop)
    · rintro (h | h)
      · exact ⟨0, by simp [ActivationKind.mergeValues], by simpa using tendsto_nhds_unique hsBot h⟩
      · exact ⟨1, by simp [ActivationKind.mergeValues], by simpa using tendsto_nhds_unique hsTop h⟩
  | tanh =>
    -- tanh is `2 σ(2t) - 1`
    have hT : ∀ t, ActivationKind.fn .tanh t = 2 * Real.sigmoid (2 * t) - 1 :=
      Real.tanh_eq_sigmoid
    have hTop : Tendsto (ActivationKind.fn .tanh) atTop (𝓝 1) := by
      have h := ((hsTop.comp (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ) < 2))).const_mul
        2).sub_const 1
      have h' : Tendsto (ActivationKind.fn .tanh) atTop (𝓝 (2 * 1 - 1)) :=
        h.congr fun t => (hT t).symm
      norm_num at h'
      exact h'
    -- and at the other end
    have hBot : Tendsto (ActivationKind.fn .tanh) atBot (𝓝 (-1)) := by
      have h := ((hsBot.comp (tendsto_id.const_mul_atBot (by norm_num : (0:ℝ) < 2))).const_mul
        2).sub_const 1
      have h' : Tendsto (ActivationKind.fn .tanh) atBot (𝓝 (2 * 0 - 1)) :=
        h.congr fun t => (hT t).symm
      norm_num at h'
      exact h'
    -- the limits are `-1` and `1`
    constructor
    · rintro ⟨z, hz, rfl⟩
      simp [ActivationKind.mergeValues] at hz
      rcases hz with rfl | rfl
      · exact Or.inl (by simpa [ActivationKind.fn] using hBot)
      · exact Or.inr (by simpa using hTop)
    · rintro (h | h)
      · exact ⟨-1, by simp [ActivationKind.mergeValues], by simpa using tendsto_nhds_unique hBot h⟩
      · exact ⟨1, by simp [ActivationKind.mergeValues], by simpa using tendsto_nhds_unique hTop h⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
