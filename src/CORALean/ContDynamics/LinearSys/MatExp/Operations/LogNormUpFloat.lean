module

public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# `MatExp.logNormUpFloat`, an upper bound of a balanced logarithmic norm

The `l∞` logarithmic norm of `S⁻¹ A S`, `S = diag s`: the largest `a_jj + Σ_{k≠j} |a_jk| s_k / s_j`.
Each term is rounded up, each row summed by `sumUp` (the diagonal's place a `zero`) and its diagonal
entry added rounded up, the rows maxed by `maximumOver`. It bounds the growth of `e^{tA}` in the
balanced norm by `e^{tμ}` (`MatExp.norm_scaleConj_exp_le_logNormUpFloat`); for the heat equation's
`A` it is `0` up to rounding, so that growth is none.

## Inputs
* `A` – float matrix
* `s` – positive float scales

## Output
* float upper bound of the balanced logarithmic norm
-/

-- Authors:       Claude Opus 5.5
-- Written:       17-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `maxⱼ (a_jj + Σ_{k≠j} |a_jk| s_k / s_j)`, every operation rounded up. -/
def MatExp.logNormUpFloat (A : Mat 𝕋 n n) (s : Vec 𝕋 n) : 𝕋 :=
  maximumOver fun j => addUp (A j j)
    (sumUp fun k => if k = j then zero else divUp (mulUp (absolute (A j k)) (s k)) (s j))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
