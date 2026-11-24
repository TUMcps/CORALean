module

public import CORALean.NN.Definitions.IntervalChainFloat
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Times
public import CORALean.ContSet.Interval.Float.Operations.Materialise
public import CORALean.Global.StepOf

@[expose] public section

/-!
# The interval batch backpropagation of a float interval chain
`Real.IntervalChain.backprop` on boxes, with every real quantity enclosed by a box of floats and
every operation outward-rounded. Each quantity of the real recursion has its box: the interval the
layer received `p = (l, u)`, and the gradients `(gl, gu)` at its output. The linear layer's
`dmu = Wᵀ (gu + gl)/2`, `dr = |W|ᵀ (gu - gl)/2`, `gl ← dmu - dr`, `gu ← dmu + dr` are
`Interval.mtimes` of the transposed float matrices; the activation's `gl ← σ'(l) ⊙ gl`,
`gu ← σ'(u) ⊙ gu` is `Interval.times` of the stored derivative enclosure `σ'E`, entrywise,
against the gradient box. The forward boxes `p` are those of `IntervalChain.fwd`. As in the real
row there is no weight update. The code runs `step_backpropImpl`, the same pass with every box
stored (`materialise`).

## Inputs
* none

## Output
* float box of input gradients from the box of output gradients
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   24-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The pass with each layer's boxes stored, which the compiled code runs: a layer reads the boxes
around it once per entry rather than once per path (`IntervalChain.backprop_eq_impl`). -/
@[step_of IntervalChain.backprop]
def IntervalChain.step_backpropImpl : ∀ {n k : ℕ}, IntervalChain 𝕋 n k →
    Interval (Vec 𝕋 n) × Interval (Vec 𝕋 n) → Interval (Vec 𝕋 k) × Interval (Vec 𝕋 k) →
      Interval (Vec 𝕋 n) × Interval (Vec 𝕋 n)
  | _, _, .nil, _, g => g
  | _, _, .linear W b rest, p, g =>
    -- the layer's output interval, the rest's gradients there, and the transposed rule
    let mu := (Interval.plus (Interval.mtimes W (Interval.halve (Interval.plus p.1 p.2)))
      ⟨b, b⟩).materialise
    let r :=
      (Interval.mtimes (W.map absolute) (Interval.halve (Interval.minus p.2 p.1))).materialise
    let g' := rest.step_backpropImpl ((Interval.minus mu r).materialise,
      (Interval.plus mu r).materialise) g
    let dmu := (Interval.mtimes Wᵀ (Interval.halve (Interval.plus g'.2 g'.1))).materialise
    let dr := (Interval.mtimes (W.map absolute)ᵀ
      (Interval.halve (Interval.minus g'.2 g'.1))).materialise
    ((Interval.minus dmu dr).materialise, (Interval.plus dmu dr).materialise)
  | _, _, .act σE σ'E rest, p, g =>
    -- the rest's gradients at the activation's output, scaled by its derivative
    let g' := rest.step_backpropImpl
      (⟨fun i => (σE ⟨p.1.inf i, p.1.sup i⟩).inf, fun i => (σE ⟨p.1.inf i, p.1.sup i⟩).sup⟩,
        ⟨fun i => (σE ⟨p.2.inf i, p.2.sup i⟩).inf, fun i => (σE ⟨p.2.inf i, p.2.sup i⟩).sup⟩) g
    ((Interval.times
        ⟨fun i => (σ'E ⟨p.1.inf i, p.1.sup i⟩).inf, fun i => (σ'E ⟨p.1.inf i, p.1.sup i⟩).sup⟩
        g'.1).materialise,
      (Interval.times
        ⟨fun i => (σ'E ⟨p.2.inf i, p.2.sup i⟩).inf, fun i => (σ'E ⟨p.2.inf i, p.2.sup i⟩).sup⟩
        g'.2).materialise)


-- =====================================  MAIN DEFINITION  ====================================== --

def IntervalChain.backprop : ∀ {n k : ℕ}, IntervalChain 𝕋 n k →
    Interval (Vec 𝕋 n) × Interval (Vec 𝕋 n) → Interval (Vec 𝕋 k) × Interval (Vec 𝕋 k) →
      Interval (Vec 𝕋 n) × Interval (Vec 𝕋 n)
  | _, _, .nil, _, g => g
  | _, _, .linear W b rest, p, g =>
    -- the layer's output interval, the rest's gradients there, and the transposed rule
    let mu := Interval.plus (Interval.mtimes W (Interval.halve (Interval.plus p.1 p.2)))
      ⟨b, b⟩
    let r := Interval.mtimes (W.map absolute) (Interval.halve (Interval.minus p.2 p.1))
    let g' := rest.backprop (Interval.minus mu r, Interval.plus mu r) g
    let dmu := Interval.mtimes Wᵀ (Interval.halve (Interval.plus g'.2 g'.1))
    let dr := Interval.mtimes (W.map absolute)ᵀ (Interval.halve (Interval.minus g'.2 g'.1))
    (Interval.minus dmu dr, Interval.plus dmu dr)
  | _, _, .act σE σ'E rest, p, g =>
    let g' := rest.backprop
      (⟨fun i => (σE ⟨p.1.inf i, p.1.sup i⟩).inf, fun i => (σE ⟨p.1.inf i, p.1.sup i⟩).sup⟩,
        ⟨fun i => (σE ⟨p.2.inf i, p.2.sup i⟩).inf, fun i => (σE ⟨p.2.inf i, p.2.sup i⟩).sup⟩) g
    (Interval.times
        ⟨fun i => (σ'E ⟨p.1.inf i, p.1.sup i⟩).inf, fun i => (σ'E ⟨p.1.inf i, p.1.sup i⟩).sup⟩
        g'.1,
      Interval.times
        ⟨fun i => (σ'E ⟨p.2.inf i, p.2.sup i⟩).inf, fun i => (σ'E ⟨p.2.inf i, p.2.sup i⟩).sup⟩
        g'.2)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
