module

public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# The error box of a float star set after one ReLU neuron

The ReLU is `1`-Lipschitz, so a point of the star set moved by an error `e` is, after the ReLU at
neuron `j`, within `|e_j|` of the image of the point without it. The box keeps its other
coordinates and widens coordinate `j` to the symmetric interval of radius `max(-inf_j, sup_j)`,
which contains every error the box held there and so every change the ReLU can make to one.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Float Float.FloatOps

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The error box with coordinate `j` made symmetric about `0`. -/
def StarSet.reluError (e : Interval (Vec 𝕋 n)) (j : Fin n) : Interval (Vec 𝕋 n) :=
  let r := maximum (neg (e.inf j)) (e.sup j)
  ⟨Function.update e.inf j (neg r), Function.update e.sup j r⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
