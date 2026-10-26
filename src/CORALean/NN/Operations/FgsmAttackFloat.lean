module

public import CORALean.NN.Operations.IntervalChainBackpropAtFloat
public import CORALean.NN.Operations.IntervalChainFwdFloat
public import CORALean.ContSet.Interval.Float.Operations.Sign
public import CORALean.ContSet.Interval.Float.Operations.Times
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Point

@[expose] public section

/-!
# `computeFGSMAttack` of a float interval chain
CORA's `computeFGSMAttack` in floats: `y = evaluate(x)` is the box of `IntervalChain.fwd` at the
degenerate pair `(X, X)`, `grad = backprop(lossDer(t, y))` the box of `IntervalChain.backpropAt`,
and `z = x + ε .* sign(grad)` the box sum of `X` and the entrywise product of the step box `ε` and
`Interval.sign` of the gradient box, a coordinate whose gradient box contains `0` getting `[-1, 1]`.
The loss derivative is an enclosure supplied as CORA's `lossDer` is, a function of two boxes. A
numeric attack is the point boxes of `x` and `ε`; the box inputs let the result feed a next pass.

## Inputs
* `n` – input width
* `m` – output width
* `c` – float interval chain
* `X` – float box of input points
* `t` – float target output
* `ε` – float box of the step size
* `lossDerF` – interval extension of the derivative of the loss

## Output
* float box enclosing the input points after one signed gradient step
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def IntervalChain.fgsmAttack {n m : ℕ} (c : IntervalChain 𝕋 n m) (X : Interval (Vec 𝕋 n))
    (t : Vec 𝕋 m) (ε : Interval 𝕋)
    (lossDerF : Interval (Vec 𝕋 m) → Interval (Vec 𝕋 m) → Interval (Vec 𝕋 m)) :
    Interval (Vec 𝕋 n) :=
  let y := (c.fwd (X, X)).1                                              -- y = evaluate(x)
  let grad := c.backpropAt X (lossDerF (Interval.point t) y)             -- backprop(lossDer(t, y))
  Interval.plus X
    (Interval.times ⟨fun _ => ε.inf, fun _ => ε.sup⟩ grad.sign)          -- x + ε .* sign(grad)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
