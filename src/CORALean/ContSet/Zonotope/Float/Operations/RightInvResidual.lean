import CORALean.Global.Float.FloatOps

/-!
# `Zonotope.rightInvResidual`

An upper bound on `|1 - G H|` entrywise, for a generator matrix `G` (`n × h`) and a candidate
right inverse `H` (`h × n`): the larger of the two directed roundings of the entry's distance to
the identity. The rectangular counterpart of `Zonotope.methCResidual`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n h : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.rightInvResidual (G : Mat 𝕋 n h) (H : Mat 𝕋 h n) : Fin n → Fin n → 𝕋 := fun i j =>
  maximum
    (absolute (subDown (if i = j then one else zero) (dotUp (fun l => G i l) fun l => H l j)))
    (absolute (subUp (if i = j then one else zero) (dotDown (fun l => G i l) fun l => H l j)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
