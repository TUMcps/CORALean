module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# `MatExp.verifyCorrConvergedFloat`, CORA's stopping test of `aux_intmat`

CORA's `aux_intmat` stops a Taylor sum at the first term that no longer changes it:
`all(Asum_add_pos <= eps*Asum_pos)` and `all(Asum_add_neg >= eps*Asum_neg)`, `eps = 2^-52`. Here
the same test on the term's box against the box of the sums, the products rounded in the
direction that makes the test harder to pass. It only steers where a sum stops.

## Inputs
* `S` – float box of the sums so far
* `t` – float box of the next term

## Output
* whether the term no longer changes the sums
-/

-- Authors:       Claude Opus 5.5
-- Written:       17-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's test: the term `t` no longer changes the sums `S`, entry by entry. -/
def MatExp.verifyCorrConvergedFloat (S t : Interval (Mat 𝕋 n n)) : Bool :=
  let eps : 𝕋 := Nat.iterate half 52 one                                     -- eps = 2^-52
  (List.finRange n).all fun j => (List.finRange n).all fun k =>
    le (t.sup j k) (mulUp eps (S.sup j k)) && le (mulDown eps (S.inf j k)) (t.inf j k)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
