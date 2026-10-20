module

public import CORALean.NN.Layers.Definitions.Relu
public import CORALean.ContSet.StarSet.Real.Instances
public import CORALean.ContSet.HPolytope.Real.Operations.Fullspace
public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import CORALean.NN.Layers.Operations.StarSetReluNeuron

@[expose] public section

/-!
# The bounds of one neuron as CORA's code computes them

`nnReLULayer/evaluateConZonotopeNeuron` computes `c_ = c(j) + 0.5 * G(j,:) * (u_ - l_)`, `G_ = 0.5 *
G(j,:) * diag(u_-l_)`, `l = c_ - sum(abs(G_))`, `u = c_ + sum(abs(G_))`. The center of the factor
box is `(l_ + u_)/2`, not `(u_ - l_)/2`: with `l_ = -1`, `u_ = 1`, as `conversionConZonoStarSet`
returns, the interval is the true one shifted by `sum(G(j,:))`. Read from the source, not run.

For the star set `(x₀, x₁) = (α, -α)`, `α ∈ [-1, 1]`, neuron `0` gets the bounds `[0, 2]` instead of
`[-1, 1]`, so `0 ≤ l` and the step leaves the set as it is, although the point `α = -1` is not on
the line after the ReLU at neuron `0`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* some point's ReLU image at the first neuron lies outside the star set after CORA's step
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- The model: CORA's code as printed, kept only to be refuted.
noncomputable def StarSet.coraRowBounds {n : ℕ} (s : StarSet ℋ𝒫 n) (j : Fin n) :
    Interval ℝ :=
  let c_ := s.c j + (1 / 2) * ∑ k, s.G j k * (s.dom.sup k - s.dom.inf k)
  let r := ∑ k, |(1 / 2) * s.G j k * (s.dom.sup k - s.dom.inf k)|
  ⟨c_ - r, c_ + r⟩


open ContSet


-- =======================================  MAIN THEOREM  ======================================= --

theorem StarSet.coraRowBounds_unsound :
    ∃ (s : StarSet ℋ𝒫 2) (x : Vec ℝ 2), x ∈ construct s ∧
      (Function.update x 0 (Real.relu (x 0)) : Vec ℝ 2)
        ∉ construct (s.reluNeuron 0 (s.coraRowBounds 0)) := by -- --- PROOF ---
  let s : StarSet ℋ𝒫 2 :=
    { m := 1, c := fun _ => 0, G := fun i _ => if i = 0 then 1 else -1,
      dom := ⟨fun _ => -1, fun _ => 1⟩, pred := HPolytope.fullspace (Vec ℝ 1) }
  have hb : s.coraRowBounds 0 = ⟨0, 2⟩ := by
    simp only [StarSet.coraRowBounds, s]
    norm_num [abs_of_nonneg]
  have hs : s.reluNeuron 0 (s.coraRowBounds 0) = s := by
    rw [hb]; simp [StarSet.reluNeuron]
  refine ⟨s, fun i => if i = 0 then -1 else 1, ⟨fun _ => -1, ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro k; show (-1 : ℝ) ≤ -1 ∧ (-1 : ℝ) ≤ 1; norm_num
  · exact ⟨fun i => i.elim0, fun i => i.elim0⟩
  · intro i; fin_cases i <;> simp [s]
  · rw [hs]
    rintro ⟨α, -, h⟩
    have h0 := h 0
    have h1 := h 1
    simp [s, Real.relu] at h0 h1
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
