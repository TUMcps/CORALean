module

public import CORALean.ContDynamics.NonlinearARX.NonlinearARX

@[expose] public section

/-!
# One sampled run of a nonlinear ARX model

`simulate` samples one run rather than enclosing all of them: a point computation, carrying
none of `reach`'s set instances. CORA's `nonlinearARX/simulate`: the first `p` outputs are the
initial window `y₀`, whose block `k` holds `y(k)`, and every later one is
`y(k) = f(y(k-1), …, y(k-p), u(k), …, u(k-p))`, which `Trajectory.step` states.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {dy du p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One sampled run from the initial window `y₀` under the input signal `u`. -/
def NonlinearARX.simulate (sys : NonlinearARX dy du p) (y₀ : Vec ℝ (p * dy)) (u : ℕ → Vec ℝ du)
    (k : ℕ) : Vec ℝ dy :=
  if hk : k < p then
    -- the first `p` outputs are the initial window's blocks
    fun b => y₀ (finProdFinEquiv (⟨k, hk⟩, b))
  else
    let pastOutputs : Vec ℝ (p * dy) := fun r =>
      sys.simulate y₀ u (k - ((finProdFinEquiv.symm r).1 + 1)) (finProdFinEquiv.symm r).2
    let pastInputs := NonlinearARX.pastIn p u k
    sys.f pastOutputs pastInputs
termination_by k
decreasing_by
  have := (finProdFinEquiv.symm r).1.isLt
  omega

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
