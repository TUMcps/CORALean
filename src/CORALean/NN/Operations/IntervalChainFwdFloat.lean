module

public import CORALean.NN.Definitions.IntervalChainFloat
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Times

@[expose] public section

/-!
# The forward pass of a float interval chain
`Real.IntervalChain.fwd` on boxes: the box of vectors the input interval's lower and upper bound
range over is carried through each layer by outward-rounded interval arithmetic. The linear layer's
`mu = W (l + u)/2 + b`, `r = |W| (u - l)/2` are `Interval.mtimes` of the float `W` and `|W|`
(`absolute` entrywise, exact) against the halved sum and difference, read back as
`[mu - r, mu + r]`; the activation's is the stored scalar enclosure `σE`, entrywise.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def IntervalChain.fwd : ∀ {n k : ℕ}, IntervalChain 𝕋 n k →
    Interval (Vec 𝕋 n) × Interval (Vec 𝕋 n) → Interval (Vec 𝕋 k) × Interval (Vec 𝕋 k)
  | _, _, .nil, p => p
  | _, _, .linear W b rest, p =>
    let mu := Interval.plus (Interval.mtimes W (Interval.halve (Interval.plus p.1 p.2)))
      ⟨b, b⟩
    let r := Interval.mtimes (W.map absolute) (Interval.halve (Interval.minus p.2 p.1))
    rest.fwd (Interval.minus mu r, Interval.plus mu r)
  | _, _, .act σE _ rest, p =>
    rest.fwd (⟨fun i => (σE ⟨p.1.inf i, p.1.sup i⟩).inf, fun i => (σE ⟨p.1.inf i, p.1.sup i⟩).sup⟩,
      ⟨fun i => (σE ⟨p.2.inf i, p.2.sup i⟩).inf, fun i => (σE ⟨p.2.inf i, p.2.sup i⟩).sup⟩)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
