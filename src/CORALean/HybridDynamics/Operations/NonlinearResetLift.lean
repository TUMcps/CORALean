module

public import CORALean.HybridDynamics.Definitions.NonlinearReset

@[expose] public section

/-!
# `NonlinearReset.lift`

CORA's `nonlinearReset/lift`: a reset on `ℝⁿ → ℝⁿ` as one on a larger space, where the state
coordinates `stateBind` and input coordinates `inputBind` of the new space feed the old reset and
its result is written back to `stateBind`. The coordinates outside `stateBind` keep their value if
`id` holds and are `0` otherwise. Assignments run in order, so for a repeated `stateBind` entry the
last one wins, as in CORA. CORA's `N` and `M` count one coordinate less than the dimension, which
here is `N` and `M` themselves.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def NonlinearReset.lift (r : NonlinearReset n m n) (N M : ℕ) (stateBind : Fin n → Fin N)
    (inputBind : Fin m → Fin M) (id : Bool) : NonlinearReset N M N where
  f := fun x u =>
    -- `f_sym = x_new(1:end-1)` or `zeros(N, 1)`
    let fSym : Vec ℝ N := if id then x else fun _ => 0
    -- `f_sym_old` at the bound coordinates
    let fSymOld : Vec ℝ n := r.f (fun j => x (stateBind j)) (fun k => u (inputBind k))
    -- `f_sym(stateBind) = subs(f_sym_old, ...)`
    (List.finRange n).foldl (fun acc j => Function.update acc (stateBind j) (fSymOld j)) fSym

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
