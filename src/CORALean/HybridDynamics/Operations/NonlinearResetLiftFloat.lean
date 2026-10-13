import CORALean.HybridDynamics.Definitions.NonlinearResetFloatModel
import CORALean.Global.Float.FloatOps

/-!
# `NonlinearReset.lift` for a float model

CORA's `nonlinearReset/lift` on the interval extension of the reset: the boxes of the larger space
are cut down to the coordinates `stateBind` and `inputBind` the old reset reads, its box is written
back to `stateBind`, and the coordinates outside it keep their box if `id` holds and are the
origin otherwise. Assignments run in order, so for a repeated `stateBind` entry the last one wins,
as in the real `lift`. It only places existing bounds and `0`, so no rounding enters.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def NonlinearReset.FloatModel.lift (fm : NonlinearReset.FloatModel 𝕋 n m n) (N M : ℕ)
    (stateBind : Fin n → Fin N) (inputBind : Fin m → Fin M) (id : Bool) :
    NonlinearReset.FloatModel 𝕋 N M N where
  f := fun X U =>
    -- the boxes the old reset reads
    let Y := fm.f ⟨fun j => X.inf (stateBind j), fun j => X.sup (stateBind j)⟩
      ⟨fun k => U.inf (inputBind k), fun k => U.sup (inputBind k)⟩
    -- the last old coordinate written to the new coordinate `i`, if any
    let src : Fin N → Option (Fin n) := fun i =>
      (List.finRange n).reverse.find? (fun j => stateBind j == i)
    ⟨fun i => match src i with
      | some j => Y.inf j
      | none => if id then X.inf i else zero,
     fun i => match src i with
      | some j => Y.sup j
      | none => if id then X.sup i else zero⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
