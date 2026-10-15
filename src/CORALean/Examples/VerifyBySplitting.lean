import CORALean.ContSet.Interval.Float.Instances
import CORALean.ContSet.Interval.Float.Theorems.SplitAtCover
import CORALean.ContSet.HPolytope.Float.Instances
import CORALean.Global.Float.Instances.Dyadic.Instances
import CORALean.NN.Instances
import CORALean.NN.Layers.Instances
import CORALean.NN.Layers.Operations.Basic
import CORALean.NN.Layers.Operations.ReluSlope
import CORALean.NN.Theorems.VerifySplitSound
import CORALean.Specification.Instances

/-!
# Splitting the input verifies what the whole box cannot

The network is `y = relu(x) + relu(-x)`, which is `|x|`, on the input box `[-1, 1]`, and the
specification is `y ≤ 1`. It holds, since `|x| ≤ 1` there, but the box enclosure does not find it:
the affine layer `x ↦ (x, -x)` is enclosed by `[-1, 1] × [-1, 1]`, which forgets that the two
coordinates are tied to each other, the ReLUs map that to `[0, 1] × [0, 1]`, and their sum is
`[0, 2]`, past the bound. So `verifySplit` at depth `0` answers `false`.

Splitting `x` at `0` removes the dependency: on `[-1, 0]` the first neuron is the constant `0`
and on `[0, 1]` the second, so each half's enclosure is `[0, 1]` and `y ≤ 1` is
found. At depth `1` the answer is `true`. Both verdicts are computed, at `Dyadic 24`, by
`rfl`; the box and its two halves are exact in that format, so no rounding enters.

`verifySplit_sound` turns the `true` into the specification on the network's exact image of the
whole box. A `false` carries nothing: it says only that this depth did not find a proof, which is
all depth `0` says here, since the specification holds.
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open CORALean ContSet
open scoped Matrix

/-- Everything below is at binary32's precision; every number used is a small dyadic. -/
abbrev Example.D := Dyadic 24

/-- `x ↦ (x, -x)`, then the two ReLUs, then their sum: `x ↦ relu(x) + relu(-x)`. -/
def Example.nn : NeuralNetwork ℐ𝒱[Example.D] 1 1 :=
  .layer (⟨fun i _ => if i = 0 then ⟨1, 0⟩ else ⟨-1, 0⟩, fun _ => ⟨0, 0⟩⟩ :
      LinearLayer Example.D 1 2)
    (.layer (⟨reluSlope, rfl⟩ : ReluLayer Example.D 2 2)
      (.layer (⟨fun _ _ => ⟨1, 0⟩, fun _ => ⟨0, 0⟩⟩ : LinearLayer Example.D 2 1) .output))

/-- The input box `[-1, 1]`. -/
def Example.input : Interval (Vec Example.D 1) := ⟨fun _ => ⟨-1, 0⟩, fun _ => ⟨1, 0⟩⟩

/-- Safe: `y ≤ 1`, as the one-row halfspace polytope. -/
def Example.spec : Specification (HPolytope Example.D (Vec Example.D 1)) :=
  .safeSet ⟨1, fun _ _ => ⟨1, 0⟩, fun _ => ⟨1, 0⟩, 0, fun i => i.elim0, fun i => i.elim0,
    Interval.origin _⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Bisect the one coordinate there is. -/
def Example.splitter (I : Interval (Vec Example.D 1)) :
    Interval (Vec Example.D 1) × Interval (Vec Example.D 1) :=
  I.splitAt (0 : Fin 1)

set_option maxRecDepth 100000 in
/-- Depth `0`: the box enclosure `[0, 2]` is past the bound, so nothing is verified. -/
theorem Example.depth_zero_fails :
    Example.nn.verifySplit Example.spec Example.splitter 0 Example.input = false := by
  rfl

set_option maxRecDepth 100000 in
/-- Depth `1`: each half encloses `[0, 1]`, so both pass. -/
theorem Example.depth_one_verifies :
    Example.nn.verifySplit Example.spec Example.splitter 1 Example.input = true := by
  rfl

/-- What the splitter is worth: `splitAt_cover`, at the one coordinate. -/
theorem Example.hcov (I : Interval (Vec Example.D 1)) :
    construct I ⊆ construct (Example.splitter I).1 ∪ construct (Example.splitter I).2 :=
  Interval.splitAt_cover I (0 : Fin 1)

/-- The consequence: `|x| ≤ 1` on the whole box, from the depth-`1` run alone. -/
theorem Example.holds :
    Example.spec.Holds (Example.nn.eval.out '' construct Example.input) :=
  Example.nn.verifySplit_sound Example.spec Example.splitter Example.hcov 1 Example.input
    Example.depth_one_verifies

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
