module

public import CORALean.NN.Operations.FgsmAttack

@[expose] public section

/-!
# One pass of CORA's `computePGDAttack`

Pass `q` of the loop: the step size decays if `q` is listed, then an FGSM step of that size, then
a clip to `[l, u]`. A file of its own, not a step of `pgdAttack`, since the float refinement of
`pgdAttack` compares its own pass against this one.

## Inputs
* `c` – network chain
* `t` – target output
* `l` – lower bounds of the input
* `u` – upper bounds of the input
* `stepsizeDecay` – step size decay factor
* `stepsizeDecayIter` – iterations at which the step size decays
* `lossDer` – derivative of the loss
* `q` – pass index
* `zs` – point and step size before the pass

## Output
* point and step size after the pass
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One pass `q` of the loop in `computePGDAttack`: `stepsize = stepsize * stepsizeDecay` if
`q ∈ stepsizeDecayIter`, `z = computeFGSMAttack(z, t, stepsize)`, `z = min(u, max(l, z))`. -/
noncomputable def Chain.pgdStep (c : Chain n m) (t : Vec ℝ m) (l u : Vec ℝ n)
    (stepsizeDecay : ℝ) (stepsizeDecayIter : List ℕ)
    (lossDer : Vec ℝ m → Vec ℝ m → Vec ℝ m) (q : ℕ) (zs : Vec ℝ n × ℝ) : Vec ℝ n × ℝ :=
  let stepsize := if q ∈ stepsizeDecayIter then zs.2 * stepsizeDecay else zs.2
  let z := c.fgsmAttack zs.1 t stepsize lossDer
  (fun i => min (u i) (max (l i) (z i)), stepsize)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
