import CORALean.ContSet.HPolytope.Float.HPolytope

/-!
# `HPolytope.isFullDim`, over a floating-point scalar

CORA's `@polytope/isFullDim` solves a Chebyshev linear program, which rounding cannot decide. A
sound test checks instead a point `x₀` the caller proposes (a Chebyshev centre computed anywhere):
every inequality row strictly slack, `A x₀ < b`, with `A x₀` rounded upward and the gap certified
by `ltStrict`, and every equality row strictly inside its interval, `be.inf < Ae x₀ < be.sup`,
rounded each way. `true` proves an interior point; `false` refutes nothing.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.isFullDim (P : HPolytope 𝕋 n) (x₀ : Vec 𝕋 n) : Bool :=
  (List.finRange P.m).all (fun i => ltStrict (dotUp (P.A i) x₀) (P.b i))
    && (List.finRange P.me).all fun i =>
      ltStrict (P.be.inf i) (dotDown (P.Ae i) x₀) && ltStrict (dotUp (P.Ae i) x₀) (P.be.sup i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
