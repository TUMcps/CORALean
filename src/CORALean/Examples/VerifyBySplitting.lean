import CORALean.ContSet.Interval.Real.Theorems.SplitAtCover
import CORALean.NN.Layers.Definitions.Enclosure
import CORALean.NN.Layers.Definitions.Relaxation
import CORALean.NN.Layers.Definitions.Relu
import CORALean.NN.Layers.Instances
import CORALean.NN.Layers.Operations.Relu
import CORALean.NN.Layers.Operations.ReluSlope
import CORALean.NN.Theorems.VerifySplitSound

/-!
# `verifySplit` decides nothing on its own

`verifySplit` is a pure `Bool` recursion: it owes no soundness itself, and
`verifySplit_sound` is where a caller pays for it, in exactly two currencies —
`hcheck`, that its `check` never says `true` of an output box the specification
does not hold on, and `hcov`, that its `splitter` never drops a point when it
bisects. Neither is `verifySplit`'s to prove, and a `false` result carries
neither: it only says this depth and this `splitter` failed to find them.

`Interval.splitAt` supplies the splitter and `splitAt_cover` discharges `hcov`
in one line. The network is one ReLU neuron, the one activation whose box
enclosure genuinely depends on the input's width — the reason splitting has
anything to buy at all.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

/-- One neuron, ReLU, over boxes. -/
noncomputable def Example.nn : NeuralNetwork ℐ𝒱 1 1 :=
  NeuralNetwork.ofLayer (ReluLayer.mk (𝕋 := ℝ) (n := 1) reluSlope rfl)

/-- Safe: output at most `10`. -/
def Example.spec : Specification (Vec ℝ 1) := Specification.safeSet {x | x 0 ≤ 10}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `true` exactly when the box's upper bound already meets the spec. -/
noncomputable def Example.check (I : Interval (Vec ℝ 1)) : Bool := decide (I.sup 0 ≤ (10 : ℝ))

/-- Bisect the one coordinate there is. -/
noncomputable def Example.splitter (I : Interval (Vec ℝ 1)) :
    Interval (Vec ℝ 1) × Interval (Vec ℝ 1) :=
  I.splitAt (0 : Fin 1)

/-- What `check = true` is worth: the box's own bound is the spec's. -/
theorem Example.hcheck : ∀ s : Interval (Vec ℝ 1), Example.check s = true →
    Example.spec.Holds (construct s) := by
  intro s hs x hx
  exact le_trans (hx 0).2 (of_decide_eq_true hs)

/-- What the splitter is worth: `splitAt_cover`, at the one coordinate. -/
theorem Example.hcov (I : Interval (Vec ℝ 1)) :
    construct I ⊆ construct (Example.splitter I).1 ∪ construct (Example.splitter I).2 :=
  Interval.splitAt_cover I (0 : Fin 1)

/-- A `true` run at depth `d` is the only thing this file needs to reach the
network's exact image — never a computed one, since nothing here evaluates
a real comparison. -/
example (d : ℕ) (X : Interval (Vec ℝ 1))
    (hverify : Example.nn.verifySplit Example.check Example.splitter d X = true) :
    Example.spec.Holds (Example.nn.eval.out '' construct X) :=
  Example.nn.verifySplit_sound Example.spec Example.check Example.hcheck
    Example.splitter Example.hcov d X hverify

/-- The same at any function the network is sound at, which is where a reduced
network's guarantee about its original lands. -/
example {f : Vec ℝ 1 → Vec ℝ 1} (hf : Example.nn.Sound f) (d : ℕ) (X : Interval (Vec ℝ 1))
    (hverify : Example.nn.verifySplit Example.check Example.splitter d X = true) :
    Example.spec.Holds (f '' construct X) :=
  hf.verifySplit_sound Example.spec Example.check Example.hcheck
    Example.splitter Example.hcov d X hverify

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
