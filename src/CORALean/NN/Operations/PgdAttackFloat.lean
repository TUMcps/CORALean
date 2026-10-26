module

public import CORALean.NN.Operations.FgsmAttackFloat
public import CORALean.ContSet.Interval.Float.Operations.MulLo
public import CORALean.ContSet.Interval.Float.Operations.MulHi

@[expose] public section

/-!
# `computePGDAttack` of a float interval chain
CORA's `computePGDAttack` in floats, pass by pass
as the real one: the bounds `l = max(l, x - ε)` and `u = min(u, x + ε)` as boxes (`x - ε` rounded
down for the lower end of `l` and up for its upper end, alike `x + ε` for `u`), the step size a
scalar box that the decay multiplies at the listed iterations, `IntervalChain.fgsmAttack` at the
box the previous pass left, and the clip `min(u, max(l, z))` by `minimum` and `maximum` of the
bounds (monotone in all three arguments, so lower with lower and upper with upper). The state
after pass `q` is the box and the step size in force.

## Inputs
* `c` – float interval chain
* `x` – float input point
* `t` – float target output
* `ε` – float perturbation radius
* `Q` – number of iterations
* `l` – float lower bounds of the input
* `u` – float upper bounds of the input
* `stepsize` – float initial step size
* `stepsizeDecay` – float step size decay factor
* `stepsizeDecayIter` – iterations at which the step size decays
* `lossDerF` – interval extension of the derivative of the loss

## Output
* float box enclosing the input point after the projected gradient steps
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One pass `q` of the loop in `computePGDAttack`: `stepsize = stepsize * stepsizeDecay` if
`q ∈ stepsizeDecayIter`, `z = computeFGSMAttack(z, t, stepsize)`, `z = min(u, max(l, z))`, on the
boxes `L` and `U` of the two bounds. -/
def IntervalChain.aux_pgdStep (c : IntervalChain 𝕋 n m) (t : Vec 𝕋 m) (L U : Interval (Vec 𝕋 n))
    (stepsizeDecay : 𝕋) (stepsizeDecayIter : List ℕ)
    (lossDerF : Interval (Vec 𝕋 m) → Interval (Vec 𝕋 m) → Interval (Vec 𝕋 m)) (q : ℕ)
    (zs : Interval (Vec 𝕋 n) × Interval 𝕋) : Interval (Vec 𝕋 n) × Interval 𝕋 :=
  let stepsize : Interval 𝕋 :=
    if q ∈ stepsizeDecayIter then
      ⟨Interval.mulLo zs.2.inf zs.2.sup stepsizeDecay stepsizeDecay,
        Interval.mulHi zs.2.inf zs.2.sup stepsizeDecay stepsizeDecay⟩
    else zs.2
  let z := c.fgsmAttack zs.1 t stepsize lossDerF
  (⟨fun i => minimum (U.inf i) (maximum (L.inf i) (z.inf i)),
    fun i => minimum (U.sup i) (maximum (L.sup i) (z.sup i))⟩, stepsize)

/-- The state after `q` passes, from the point `x` and the initial step size. -/
def IntervalChain.aux_pgdState (c : IntervalChain 𝕋 n m) (x : Vec 𝕋 n) (t : Vec 𝕋 m)
    (L U : Interval (Vec 𝕋 n)) (stepsize stepsizeDecay : 𝕋) (stepsizeDecayIter : List ℕ)
    (lossDerF : Interval (Vec 𝕋 m) → Interval (Vec 𝕋 m) → Interval (Vec 𝕋 m)) :
    ℕ → Interval (Vec 𝕋 n) × Interval 𝕋
  | 0 => (Interval.point x, Interval.point stepsize)
  | q + 1 => c.aux_pgdStep t L U stepsizeDecay stepsizeDecayIter lossDerF (q + 1)
      (c.aux_pgdState x t L U stepsize stepsizeDecay stepsizeDecayIter lossDerF q)


-- =====================================  MAIN DEFINITION  ====================================== --

def IntervalChain.pgdAttack (c : IntervalChain 𝕋 n m) (x : Vec 𝕋 n) (t : Vec 𝕋 m) (ε : 𝕋) (Q : ℕ)
    (l u : Vec 𝕋 n) (stepsize stepsizeDecay : 𝕋) (stepsizeDecayIter : List ℕ)
    (lossDerF : Interval (Vec 𝕋 m) → Interval (Vec 𝕋 m) → Interval (Vec 𝕋 m)) :
    Interval (Vec 𝕋 n) :=
  let L : Interval (Vec 𝕋 n) :=                                         -- l = max(l, x - ε)
    ⟨fun i => maximum (l i) (subDown (x i) ε), fun i => maximum (l i) (subUp (x i) ε)⟩
  let U : Interval (Vec 𝕋 n) :=                                         -- u = min(u, x + ε)
    ⟨fun i => minimum (u i) (addDown (x i) ε), fun i => minimum (u i) (addUp (x i) ε)⟩
  (c.aux_pgdState x t L U stepsize stepsizeDecay stepsizeDecayIter lossDerF Q).1

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
