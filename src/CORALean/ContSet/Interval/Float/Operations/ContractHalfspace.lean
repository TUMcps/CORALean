module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.contractHalfspace`

The box cut by one halfspace `a · x ≤ b`, coordinate by coordinate. The rest of
the row is bounded over the box, so `a_j x_j ≤ b - ∑_{k ≠ j} a_k x_k ≤ b + s_j`,
and dividing by `a_j` bounds `x_j` from above where `a_j > 0` and from below
where `a_j < 0`: one forward-backward pass of interval constraint propagation
on a linear constraint, every coordinate read against the box it was given.

A coefficient whose sign `ltStrict` cannot certify leaves its coordinate as it
was, `divUp` asking a divisor known to be positive. A result whose lower end
passes its upper one is a box no point lies in, which is what the cut is when
the box misses the halfspace; `representsa_emptySet` is what says so.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The box `I` cut to the halfspace `a · x ≤ b`, every coordinate on its own. -/
def Interval.contractHalfspace (I : Interval (Vec 𝕋 n)) (a : Vec 𝕋 n) (b : 𝕋) :
    Interval (Vec 𝕋 n) :=
  let s := fun j => sumUp fun k =>                                 -- s_j ≥ ∑_{k ≠ j} -a_k x_k
    if k = j then zero else maximum (mulUp (neg (a k)) (I.sup k)) (mulUp (neg (a k)) (I.inf k))
  let c := fun j => addUp b (s j)                                  -- c_j ≥ a_j x_j
  { inf := fun j => if ltStrict (a j) zero                         -- a_j < 0: x_j ≥ c_j / a_j
      then maximum (I.inf j) (neg (divUp (c j) (neg (a j)))) else I.inf j
    sup := fun j => if ltStrict zero (a j)                         -- a_j > 0: x_j ≤ c_j / a_j
      then minimum (I.sup j) (divUp (c j) (a j)) else I.sup j }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
