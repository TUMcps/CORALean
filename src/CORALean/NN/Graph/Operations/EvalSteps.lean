import CORALean.ContSet.ContSet.ContSet

/-!
# A chain of message-passing steps, at one matrix

`L` message-passing steps at a fixed matrix `Pm`, weights applied in order: the
value a graph's own iteration computes, written at a *matrix* rather than at a
set and a factor vector, which is what the soundness statement of `gcnSteps`
needs to read against.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `L` message-passing steps at a fixed matrix `Pm`, weights applied in order:
the value the chain below computes at one factor vector. -/
def GNN.evalSteps {N F : ℕ} (Pm : Mat ℝ N N) :
    ∀ (L : ℕ), (Fin L → Mat ℝ F F) → Mat ℝ N F → Mat ℝ N F
  | 0, _, h => h
  | L + 1, W, h => GNN.evalSteps Pm L (fun i => W i.succ) (Pm * h * W 0)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
