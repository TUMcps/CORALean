module

public import CORALean.ContSet.Capsule.Float.Operations.Basic

@[expose] public section

/-!
# `Capsule.isDisjoint`: a certificate that two capsules share no point

CORA's `isIntersecting_` for two capsules, answered one-sidedly: `true` only if some coordinate
separates the centres by more than the two bounding radii (`Capsule.radius`, rounded up),
`ltStrict` certifying the gap with the difference rounded down. Every point of a capsule is within
its radius of its centre, and a coordinate gap is at most the Euclidean distance, so a `true`
answer excludes a common point. `false` refutes nothing: the segment-to-segment distance of CORA's
quadratic program is not computed.
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

def Capsule.isDisjoint (k : ℕ) (C₁ C₂ : Capsule 𝕋 n) : Bool :=
  let R := addUp (C₁.radius k) (C₂.radius k)
  (List.finRange n).any fun i =>
    ltStrict R (subDown (C₁.c i) (C₂.c i)) || ltStrict R (subDown (C₂.c i) (C₁.c i))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
