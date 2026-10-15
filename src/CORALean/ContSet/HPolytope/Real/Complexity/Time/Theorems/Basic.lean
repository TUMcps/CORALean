module

public import CORALean.ContSet.HPolytope.Real.Operations.Comap
public import CORALean.Global.Cost
public import CORALean.ContSet.HPolytope.Real.Complexity.Time.Operations.ComapCost
public import CORALean.ContSet.HPolytope.Real.Operations.HalfScaled
public import CORALean.ContSet.HPolytope.Real.Complexity.Time.Operations.HalfScaledCost

@[expose] public section

/-!
# `ContSet/HPolytope/Real/Complexity/Time/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real


-- ================================  `HPolytope.comapCost_mono`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in the row counts, so a bound on the operand's size gives a bound on
the cost. -/
theorem HPolytope.comapCost_mono {m m' me me' : ℕ} (cr : Cost) (hm : m ≤ m') (hme : me ≤ me') :
    HPolytope.comapCost m me cr ≤ HPolytope.comapCost m' me' cr :=
  Nat.mul_le_mul_right _ (Nat.add_le_add hm hme)


-- =============================  `HPolytope.halfScaledCost_mono`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in the row counts and the dimension, so a bound on the operand's
size gives a bound on the cost. -/
theorem HPolytope.halfScaledCost_mono {m m' me me' d d' : ℕ} (hm : m ≤ m') (hme : me ≤ me')
    (hd : d ≤ d') : HPolytope.halfScaledCost m me d ≤ HPolytope.halfScaledCost m' me' d' :=
  Nat.mul_le_mul (Nat.add_le_add hm hme) (Nat.succ_le_succ (Nat.mul_le_mul_left _ hd))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
