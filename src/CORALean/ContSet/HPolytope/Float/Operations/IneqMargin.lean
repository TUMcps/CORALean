module

public import CORALean.ContSet.HPolytope.Float.HPolytope

@[expose] public section

/-!
# `HPolytope.ineqMargin`

A candidate radius of a ball around `β₀` inside every inequality row: the least of one and each
row's room, its bound with its slack less its reading of `β₀` (rounded down), over the row's
absolute sum (rounded down), a row that is zero leaving room one. Nothing is trusted about it:
`HPolytope.ineqsContainBall` checks the radius it is given, and a bad candidate fails there.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A room `s` over a row sum `r`, one where the row is zero. -/
def HPolytope.aux_ratio (s r : 𝕋) : 𝕋 := if ltStrict zero r then divDown s r else one


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The least room, over its row's absolute sum, of the inequality rows at `β₀`, at most one. -/
def HPolytope.ineqMargin (P : HPolytope 𝕋 (Vec 𝕋 n)) (β₀ : Vec 𝕋 n) : 𝕋 :=
  (List.finRange P.m).foldl (fun acc i => minimum acc (HPolytope.aux_ratio
    (subDown (addDown (P.b i) (absolute (P.b_error i))) (dotUp (P.A i) β₀)) (radius P.A i))) one

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
