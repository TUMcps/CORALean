module

public import CORALean.ContSet.Taylm.Real.Operations.Compose
public import CORALean.ContSet.Taylm.Real.Operations.Reach
public import CORALean.ContSet.Taylm.Real.Operations.ConstCoef
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

@[expose] public section

/-!
# `Taylm.invTight`

The multiplicative inverse with the remainder of [1, Eq. 38], a choice between the Lagrange
remainder `L_q` of eq. (33) and the exact remainder `R_q(B(T), c_f)` of eq. (34). As printed,
`L_q` is taken if it lies in `1/B(T)`, which never happens (`1/B(T)` excludes `0`, `L_q` holds it);
the test here is CORA's (`priv_inverse`): `R_q` once `L_q` reaches past `1/B(T)` at both ends.
Both in magnitude: `L_q` as `Taylm.inv` bounds it, `rᴺ⁺¹/mᴺ⁺²`, and `R_q` through its closed form
`|x - c|ᴺ⁺¹/(|x| |c|ᴺ⁺¹) ≤ rᴺ⁺¹/(m |c|ᴺ⁺¹)`, where the source evaluates the recursion of eqs.
(36)-(37) in interval arithmetic.

## References

* [1] M. Althoff, D. Grebenyuk, and N. Kochdumper. "Implementation of Taylor Models in CORA
      2018". In Proc. of the 5th International Workshop on Applied Verification of Continuous
      and Hybrid Systems (ARCH18), EPiC Series in Computing, vol. 54, pp. 145-173, 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.invTight (T : Taylm n) : Taylm n :=
  let c := T.constCoef
  let N := T.maxOrder
  -- the distance of the hull from zero, and the reach of the range from the centre
  let m := max (min c T.bounds.1) (-max c T.bounds.2)
  let r := T.reach c
  -- (33): `L_q`, the Lagrange remainder, in magnitude
  let ρL := r ^ (N + 1) / m ^ (N + 2)
  -- (34): `R_q(B(T), c_f)`, the exact remainder, in magnitude
  let ρR := r ^ (N + 1) / (m * |c| ^ (N + 1))
  -- (38): `R_q` once `L_q` reaches past `1/B(T)` at both ends, `L_q` otherwise
  let ρ := if -ρL < 1 / T.bounds.2 ∧ 1 / T.bounds.1 < ρL then ρR else ρL
  T.compose c (fun k => iteratedDeriv k (fun x => x⁻¹) c / (k.factorial : ℝ)) N ρ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
