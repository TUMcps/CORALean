module

public import CORALean.ContDynamics.LinearSys.Definitions.VerifyZonoGenSet

@[expose] public section

/-!
# The generators of two lists span the sums

A point spanned by `L₁` plus a point spanned by `L₂` is spanned by `L₁ ++ L₂`: the coefficients of
the two lists side by side.

## Inputs
* `L₁` – first generators
* `L₂` – second generators
* `x` – point spanned by the first
* `y` – point spanned by the second

## Hypotheses
* `hx` – `x` is spanned by `L₁`
* `hy` – `y` is spanned by `L₂`

## Conclusion
* `x + y` is spanned by `L₁ ++ L₂`
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.add_mem_verifyZonoGenSet_append {L₁ L₂ : List (Vec ℝ q)} {x y : Vec ℝ q}
    (hx : x ∈ LinearSys.verifyZonoGenSet L₁)
    (hy : y ∈ LinearSys.verifyZonoGenSet L₂) : -- --- CONCL ---
    x + y ∈ LinearSys.verifyZonoGenSet (L₁ ++ L₂) := by -- --- PROOF ---
  induction L₁ generalizing x with
  | nil =>
    -- `x = 0`
    have hx0 : x = 0 := hx
    rw [hx0, zero_add]
    exact hy
  | cons g L ih =>
    -- `x = β g + x'`: keep `β g`, carry `x' + y`
    obtain ⟨β, hβ, x', hx', rfl⟩ := hx
    exact ⟨β, hβ, x' + y, ih hx', by rw [add_assoc]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
