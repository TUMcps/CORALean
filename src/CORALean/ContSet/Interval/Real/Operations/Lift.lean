import CORALean.ContSet.Interval.Real.Operations.EBox

/-!
# `Interval.lift_`

CORA's `@interval/lift_`: the box placed into the coordinates `proj` of `ℝᴺ`, every other
coordinate `(-∞, ∞)`: `lb = -inf(N,1); ub = inf(N,1); lb(proj) = I.inf; ub(proj) = I.sup`. Its
bounds are infinite off `proj`, so the result is an `Interval.EBox`. CORA throws on an empty
interval; no throw here, the theorem needs no case split.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

open Classical in
noncomputable def Interval.lift_ (I : Interval (Vec ℝ m)) (N : ℕ) (proj : Fin m → Fin N) :
    Interval.EBox N :=
  let lb : Fin N → EReal := fun _ => ⊥
  let ub : Fin N → EReal := fun _ => ⊤
  let lb' : Fin N → EReal := Function.extend proj (fun i => ((I.inf i : ℝ) : EReal)) lb
  let ub' : Fin N → EReal := Function.extend proj (fun i => ((I.sup i : ℝ) : EReal)) ub
  (lb', ub')

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
