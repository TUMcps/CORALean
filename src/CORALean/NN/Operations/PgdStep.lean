import CORALean.NN.Operations.FgsmAttack

/-!
# One iteration of CORA's `computePGDAttack`

The loop body: the step size decays when the iteration is listed, one FGSM step of that size
from the current point, then the values are clipped to `[l, u]`. The state is the point and the
step size, which the decay changes.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


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
