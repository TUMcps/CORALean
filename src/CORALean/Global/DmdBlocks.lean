module

public import CORALean.Global.DmdRegressor

@[expose] public section

/-!
# The blocks of an identified matrix

`A = Alist{i}(:,1:n)`, `c = Alist{i}(:,n+1)`, `B = Alist{i}(:,n+2:end)` of `priv_identifyDMD`.
The source is [1].

## Inputs
* `M` – stacked matrix `[A c B]`

## Output
* the state, input and offset blocks

## References

* [1] `contDynamics/@linearSysDT/private/priv_identifyDMD.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `(A, B, c)` from `[A c B]`. -/
def dmdBlocks (M : Mat ℝ n (n + 1 + m)) : Mat ℝ n n × Mat ℝ n m × Vec ℝ n :=
  (fun i j => M i (Fin.castAdd m (Fin.castSucc j)),
    fun i k => M i (Fin.natAdd (n + 1) k),
    fun i => M i (Fin.castAdd m (Fin.last n)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
