import CORALean.ContSet.ConZonotope.Float.ConZonotope

/-!
# `ConZonotope.interiorMargin`

A candidate margin for a coefficient vector `β₀` strictly inside a float constrained zonotope's
coefficient polytope: half the least of one, the unit box's slack `1 - |β₀ⱼ|` and each constraint
row's slack over the row's absolute sum (the slack rounded down, the quotient rounded down), so
that a ball of that radius in the supremum norm stays inside. Nothing is trusted about it:
`ConZonotope.interiorCert` checks the margin it is given, and a bad candidate costs the `true`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A slack `s` over a row sum `r`, one where the row is zero. -/
def ConZonotope.aux_ratio (s r : 𝕋) : 𝕋 := if ltStrict zero r then divDown s r else one


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.interiorMargin (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (β₀ : Vec 𝕋 cZ.h) : 𝕋 :=
  let box := (List.finRange cZ.h).foldl
    (fun acc j => minimum acc (subDown one (absolute (β₀ j)))) one
  let ineq := (List.finRange cZ.P.m).foldl
    (fun acc i => minimum acc (ConZonotope.aux_ratio
      (subDown (cZ.P.b i) (dotUp (cZ.P.A i) β₀)) (radius cZ.P.A i))) box
  let eq := (List.finRange cZ.P.me).foldl
    (fun acc i => minimum (minimum acc (ConZonotope.aux_ratio
        (subDown (cZ.P.be.sup i) (dotUp (cZ.P.Ae i) β₀)) (radius cZ.P.Ae i)))
      (ConZonotope.aux_ratio
        (subDown (dotDown (cZ.P.Ae i) β₀) (cZ.P.be.inf i)) (radius cZ.P.Ae i))) ineq
  half eq

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
