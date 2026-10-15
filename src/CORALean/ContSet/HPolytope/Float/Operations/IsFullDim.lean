module

public import CORALean.ContSet.HPolytope.Float.HPolytope

@[expose] public section

/-!
# `HPolytope.isFullDim`, over a floating-point scalar

CORA's `@polytope/isFullDim` solves a Chebyshev linear program, which rounding cannot decide. A
sound test checks instead a point `x₀` the caller proposes (a Chebyshev centre computed anywhere):
there is no equality row (an equality pins the set to a hyperplane), every inequality row is
strictly slack, `A x₀ < b`, with `A x₀` rounded upward and the gap certified by `ltStrict`, and the
error box is not empty, `inf ≤ sup` in every coordinate. `true` proves an interior point; `false`
refutes nothing.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       04-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.isFullDim (P : HPolytope 𝕋 (Vec 𝕋 n)) (x₀ : Vec 𝕋 n) : Bool :=
  (P.me == 0) && (List.finRange P.m).all (fun i => ltStrict (dotUp (P.A i) x₀) (P.b i))
    && (List.finRange n).all fun j => le (P.I_error.inf j) (P.I_error.sup j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
