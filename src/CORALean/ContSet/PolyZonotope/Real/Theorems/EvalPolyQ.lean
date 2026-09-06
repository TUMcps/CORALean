import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPoly

/-!
# `PolyZonotope.evalPoly` leaves no independent block

`mul` sets `q := 0` and the empty accumulator starts there, so every Horner step
keeps it. Stated because it is the hypothesis `exists_point_of_q_zero` asks for,
and that is what turns a member of the evaluated set back into a factor vector —
without it the result can only be entered, never left.

Two cases and no induction: the empty accumulator names `0` and a Horner step
names `mul`'s field, so neither case looks at what is below it.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.evalPoly_q (S : PolyZonotope (Vec ℝ n)) :
    ∀ coeffs : List (Vec ℝ n), (S.evalPoly coeffs).q = 0
  | [] => rfl
  | _ :: _ => rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
