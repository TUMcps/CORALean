module

public import CORALean.ContSet.ConZonotope.Real.Operations.OfMat

@[expose] public section

/-!
# `ConZonotope.constraintReduce`

[1, Prop. 5]'s set `Z̃ = {G − Λ_G A, c + Λ_G b, A − Λ_A A, b − Λ_A b}` (eq. 27), for any
`Λ_G ∈ ℝ^{n×nc}` and `Λ_A ∈ ℝ^{nc×nc}`. The system is the paper's `Aξ = b`, built with
`ofMat`; column `j` of `Λ_G A` is `Λ_G` applied to column `j` of `A`.

## Inputs
* `n` – dimension
* `q` – number of constraints
* `h` – number of generators
* `c` – center
* `G` – generators
* `A` – constraint matrix
* `b` – constraint offset
* `ΛG` – generator multiplier
* `ΛA` – constraint multiplier

## Output
* the constrained zonotope with the constraints reduced

## References

* [1] [J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes: A new
      tool for set-based estimation and fault detection". Automatica,
      2016.](../../../../../../references/2016/scott-automatica-constrained-zonotopes.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Prop. 5]: the constraints folded back into the generators and the center by `ΛG` and
`ΛA`; the result encloses `ofMat c G A b` for every choice. -/
noncomputable def ConZonotope.constraintReduce {n q h : ℕ} (c : Vec ℝ n)
    (G : Fin h → Vec ℝ n) (A : Mat ℝ q h) (b : Vec ℝ q) (ΛG : Mat ℝ n q) (ΛA : Mat ℝ q q) :
    ConZonotope (Vec ℝ n) :=
  ConZonotope.ofMat (c + ΛG *ᵥ b) (fun j => G j - ΛG *ᵥ fun k => A k j)   -- c + Λ_G b, G − Λ_G A
    (A - ΛA * A) (b - ΛA *ᵥ b)                                           -- A − Λ_A A, b − Λ_A b

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
