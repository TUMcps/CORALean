module

public import CORALean.ContDynamics.LinearARX.Operations.InputMat
public import CORALean.ContSet.Interval.Float.Instances
public import CORALean.ContSet.Interval.Float.Operations.Point

@[expose] public section

/-!
# The input a float ARX step feeds, as a box

`feed` of the converted state-space system, folded in float interval arithmetic as
`inputSet` does but with each lag's input held as a point interval: the `p + 1` lag
terms `inputMat j · u(k + p - j)` are summed by `plus`, in the fold order of
`inputSet`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Scalar Plus Mtimes CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {dy du p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearARX.feedBox (sys : LinearARX 𝕋 dy du p) (u : ℕ → Vec 𝕋 du) (k : ℕ) :
    Interval (Vec 𝕋 (p * dy)) :=
  (List.finRange p).foldl
    (fun acc j => plus (S := Interval (Vec 𝕋 (p * dy))) acc
      (mtimes (S := fun n => Interval (Vec 𝕋 n)) (sys.inputMat j.succ)
        (Interval.point (u (k + p - (j.succ : ℕ))))))
    (mtimes (S := fun n => Interval (Vec 𝕋 n)) (sys.inputMat 0)
      (Interval.point (u (k + p - (0 : Fin (p + 1))))))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
