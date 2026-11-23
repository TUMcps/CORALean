module

public import CORALean.Global.Tensor

@[expose] public section

/-!
# The outputs of a graph network so far

One value per output computed so far, the latest first, of the dimensions `Γ`: a layer of a graph
network names an earlier output by its place in `Γ`, `0` the one before it.

## Inputs
* `V` – the values of each dimension
* `Γ` – the dimensions of the outputs

## Output
* the type of the outputs so far
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One value per output, the latest first, of the dimensions `Γ`. -/
abbrev GraphEnv (V : ℕ → Type) (Γ : List ℕ) : Type := (i : Fin Γ.length) → V (Γ.get i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
