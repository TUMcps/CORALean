import CORALean.Global.Float.FloatOps

/-!
# `Zonotope.mulResidual`

An upper bound on `|A - G Γ|` entrywise, for `A` (`n × m`), `G` (`n × h`) and `Γ` (`h × m`): the
larger of the two directed roundings of each entry's distance. `Zonotope.rightInvResidual` is the
case `A = 1`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.mulResidual {m h : ℕ} (A : Mat 𝕋 n m) (G : Mat 𝕋 n h) (Γ : Mat 𝕋 h m) :
    Fin n → Fin m → 𝕋 := fun i j =>
  maximum (absolute (subDown (A i j) (dotUp (fun l => G i l) fun l => Γ l j)))
    (absolute (subUp (A i j) (dotDown (fun l => G i l) fun l => Γ l j)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
