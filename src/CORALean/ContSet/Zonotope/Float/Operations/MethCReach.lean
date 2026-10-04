import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# `Zonotope.methCReach`

How far `H` carries the zonotope's generators: the largest row sum of the magnitudes of
`H G`, rounded up. A point `G β` of the zonotope with `|β| ≤ 1` has `|(H G β)ᵢ|` at most this,
whichever signs `β` has. Each entry of `H G` is a dot product, in both directions.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n h : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- An upper bound on `‖H G β‖∞` over the coefficient box. -/
def Zonotope.methCReach (H : Mat 𝕋 n n) (G : Mat 𝕋 n h) : 𝕋 :=
  maximumOver fun i => sumUp fun j =>
    maximum (absolute (dotDown (H i) fun l => G l j)) (absolute (dotUp (H i) fun l => G l j))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
