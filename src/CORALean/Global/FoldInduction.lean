import CORALean.Global.Mathlib

/-!
# A property carried through `Fin.foldl`

If the initial state has a property and every step of `Fin.foldl` preserves it — for
*every* index the step is applied at, not only the one actually reached — the final
state has it too. `Fin.foldl_succ_last` peels the last step off, which is what lets the
induction go through without the state's own type depending on the loop count.

This is the induction principle a loop-shaped algorithm's soundness proof asks for: a
pass that tightens one coordinate's bound at a time is exactly such a fold, and this is
what carries "every feasible point stays inside" across the whole pass.
-/

-- Authors:       Tobias Ladner
-- Written:       21-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- A property preserved by every step of `Fin.foldl` holds of the initial state, and
so of the folded one. -/
theorem Fin.foldl_induction {α : Sort*} {P : α → Prop} :
    ∀ (n : ℕ) (f : α → Fin n → α) (x : α),
      P x → (∀ y i, P y → P (f y i)) → P (Fin.foldl n f x)
  | 0, _, x, hx, _ => by simpa using hx
  | n + 1, f, x, hx, hstep => by
      rw [Fin.foldl_succ_last]
      exact hstep _ (Fin.last n)
        (Fin.foldl_induction n (fun y i => f y i.castSucc) x hx fun y i => hstep y i.castSucc)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
