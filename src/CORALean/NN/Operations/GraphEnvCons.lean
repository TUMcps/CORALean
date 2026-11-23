module

public import CORALean.NN.Definitions.GraphEnv
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-!
# `GraphEnv.cons`

The outputs so far with a new latest one in front: place `0` is `x`, place `i + 1` is `e`'s `i`.

## Inputs
* `x` – the new output
* `e` – the outputs so far

## Output
* the outputs with `x` first
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {V : ℕ → Type} {Γ : List ℕ} {m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def GraphEnv.cons (x : V m) (e : GraphEnv V Γ) : GraphEnv V (m :: Γ) :=
  Fin.cons (α := fun i : Fin (Γ.length + 1) => V ((m :: Γ).get i)) x e

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
