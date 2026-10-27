module

public import CORALean.ContSet.HPolytope.Float.Operations.EqVec
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `HPolytope.pairsToEq`: the inverted pairs as equalities

CORA's `priv_compact_toEquality`: every pair `aᵀx ≤ b`, `-aᵀx ≤ -b` becomes the equality
`aᵀx = b`, appended after the existing equality rows with the right-hand side `b`; the rows in pairs
are deleted from the inequalities. Nothing rounds, and the error box is kept.

## Inputs
* `Q` – H-polytope

## Output
* the rows outside an inverted pair, and the lead row of each pair as an equality
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       12-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- `[aⱼ, bⱼ] = -[aᵢ, bᵢ]` and `[aᵢ, bᵢ] = -[aⱼ, bⱼ]`, each certified. -/
@[step_of HPolytope.pairsToEq]
def HPolytope.step_isInvertedPair (Q : HPolytope 𝕋 (Vec 𝕋 n)) (i j : Fin Q.m) : Bool :=
  HPolytope.eqVec (Q.A j) (-(Q.A i)) && HPolytope.eqScalar (Q.b j) (neg (Q.b i)) &&
    HPolytope.eqVec (Q.A i) (-(Q.A j)) && HPolytope.eqScalar (Q.b i) (neg (Q.b j)) &&
    (HPolytope.eqScalar (Q.b_error i) zero && HPolytope.eqScalar (Q.b_error j) zero)

/-- The rows with no inverted partner. -/
@[step_of HPolytope.pairsToEq]
def HPolytope.step_keptRows (Q : HPolytope 𝕋 (Vec 𝕋 n)) : List (Fin Q.m) :=
  (List.finRange Q.m).filter fun i =>
    !(List.finRange Q.m).any fun j => HPolytope.step_isInvertedPair Q i j

/-- The rows with an inverted partner of no smaller index. -/
@[step_of HPolytope.pairsToEq]
def HPolytope.step_leadRows (Q : HPolytope 𝕋 (Vec 𝕋 n)) : List (Fin Q.m) :=
  (List.finRange Q.m).filter fun i =>
    (List.finRange Q.m).any fun j => HPolytope.step_isInvertedPair Q i j && decide (i ≤ j)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The rows outside an inverted pair, and the lead row of each pair as an equality. -/
def HPolytope.pairsToEq (Q : HPolytope 𝕋 (Vec 𝕋 n)) : HPolytope 𝕋 (Vec 𝕋 n) where
  m := Q.step_keptRows.length
  A := fun k => Q.A (Q.step_keptRows.get k)
  b := fun k => Q.b (Q.step_keptRows.get k)
  me := Q.me + Q.step_leadRows.length
  Ae := Fin.append Q.Ae fun k => Q.A (Q.step_leadRows.get k)
  be := Fin.append Q.be fun k => Q.b (Q.step_leadRows.get k)
  b_error := fun k => Q.b_error (Q.step_keptRows.get k)
  be_error := Fin.append Q.be_error fun _ => zero
  I_error := Q.I_error

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
