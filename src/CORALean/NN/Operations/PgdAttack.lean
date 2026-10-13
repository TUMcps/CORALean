import CORALean.NN.Operations.PgdStep

/-!
# CORA's `computePGDAttack`: projected gradient descent

`l = max(l, x - ε)`, `u = min(u, x + ε)`, then `Q` passes of an FGSM step of size
`stepsize = ε / Q` (by default) followed by a clip to `[l, u]`, starting at `z = x`. Deterministic:
the body has no `rand`. The state after pass `q` is the point and the step size in force.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `computePGDAttack`, `l` and `u` the caller's bounds (CORA's default `∓∞` is the
caller's too: a real has no infinity) and `stepsize` the initial step size, `ε / Q` by default. -/
noncomputable def Chain.pgdAttack (c : Chain n m) (x : Vec ℝ n) (t : Vec ℝ m) (ε : ℝ) (Q : ℕ)
    (l u : Vec ℝ n) (stepsize stepsizeDecay : ℝ) (stepsizeDecayIter : List ℕ)
    (lossDer : Vec ℝ m → Vec ℝ m → Vec ℝ m) : Vec ℝ n :=
  let l := fun i => max (l i) (x i - ε)
  let u := fun i => min (u i) (x i + ε)
  let state : ℕ → Vec ℝ n × ℝ := fun q =>
    Nat.rec (x, stepsize)
      (fun q zs => c.pgdStep t l u stepsizeDecay stepsizeDecayIter lossDer (q + 1) zs) q
  (state Q).1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
