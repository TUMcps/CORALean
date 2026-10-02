import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Real.Basic
import CORALean.Global.Tensor

/-!
# A fold of updates leaves a coordinate none of them hits

Folding `Function.update acc (g j) (v j)` over a list of indices leaves the value at `i` alone if
no `g j` of the list equals `i`: the fact behind `NonlinearReset.lift` keeping its unbound
coordinates.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m N M : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearReset.foldl_update_of_not_mem {n N : ℕ} (g : Fin n → Fin N) (v : Fin n → ℝ)
    (i : Fin N) : ∀ (l : List (Fin n)) (base : Fin N → ℝ), (∀ j ∈ l, g j ≠ i) →
      l.foldl (fun acc j => Function.update acc (g j) (v j)) base i = base i := by -- --- PROOF ---
  -- induction on the list: each update is at a coordinate other than `i`
  intro l
  induction l with
  | nil => intro base _; rfl
  | cons a l ih =>
    intro base h
    rw [List.foldl_cons, ih _ fun j hj => h j (List.mem_cons_of_mem _ hj),
      Function.update_of_ne (Ne.symm (h a List.mem_cons_self))]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
