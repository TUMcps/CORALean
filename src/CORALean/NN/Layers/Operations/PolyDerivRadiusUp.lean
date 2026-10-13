import CORALean.NN.Layers.Operations.PowRange

/-!
# A stored fit's derivative radius, rounded up

How far the remaining monomials move the centre over the box, everything rounded up: the
degree count `i` reaches the scalar as `nsmulUp i one`, an upper bound rather than a cast,
`FloatOps` having no integer literal above one.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The remaining monomials' reach over the box, every sign against itself, rounded up. -/
def polyDerivRadiusUp (c : Fin (n + 1) → 𝕋) (l u : 𝕋) : 𝕋 :=
  sumUp fun i => if (i : ℕ) = 1 then zero
    else mulUp (mulUp (absolute (c i)) (nsmulUp (i : ℕ) one))
      (powRange (maximum (absolute l) (absolute u)) ((i : ℕ) - 1)).2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
