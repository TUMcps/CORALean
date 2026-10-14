module

public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import CORALean.NN.Layers.Operations.StarSetCoraRowBounds
public import CORALean.NN.Layers.Operations.StarSetReluNeuron

@[expose] public section

/-!
# CORA's neuron bounds make the ReLU step unsound

With the bounds `evaluateConZonotopeNeuron` computes, in `StarSet.coraRowBounds`, one neuron's step
fails to enclose the ReLU. The star set `(x₀, x₁) = (α, -α)`, `α ∈ [-1, 1]`, which is what
`conversionConZonoStarSet` returns for the zonotope with `G = [1; -1]`: neuron `0` is given the
bounds `[0, 2]` instead of `[-1, 1]`, so `0 ≤ l` and the step leaves the set as it is, although
the point `α = -1`, `(0, 1)` after the ReLU at neuron `0`, is not on the line `x₁ = -x₀`.
Read from the source, not run.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet


-- =======================================  MAIN THEOREM  ======================================= --

theorem StarSet.coraRowBounds_unsound :
    ∃ (s : StarSet 2) (x : Vec ℝ 2), x ∈ construct s ∧
      (Function.update x 0 (max (x 0) 0) : Vec ℝ 2)
        ∉ construct (s.reluNeuron 0 (s.coraRowBounds 0)) := by -- --- PROOF ---
  let s : StarSet 2 :=
    { m := 1, c := fun _ => 0, G := fun i _ => if i = 0 then 1 else -1, cons := [],
      l := fun _ => -1, u := fun _ => 1 }
  have hb : s.coraRowBounds 0 = ⟨0, 2⟩ := by
    simp only [StarSet.coraRowBounds, s]
    norm_num [abs_of_nonneg]
  have hs : s.reluNeuron 0 (s.coraRowBounds 0) = s := by
    rw [hb]; simp [StarSet.reluNeuron]
  refine ⟨s, fun i => if i = 0 then -1 else 1, ⟨fun _ => -1, ?_, ?_, ?_⟩, ?_⟩
  · intro k; simp [s]
  · intro r hr; simp [s] at hr
  · intro i; fin_cases i <;> simp [s]
  · rw [hs]
    rintro ⟨α, -, -, h⟩
    have h0 := h 0
    have h1 := h 1
    simp [s] at h0 h1
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
