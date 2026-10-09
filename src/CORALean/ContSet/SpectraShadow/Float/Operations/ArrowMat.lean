import CORALean.Global.Tensor
import CORALean.ContSet.SpectraShadow.Float.SpectraShadow

/-!
# The arrowhead matrix, over a floating-point scalar

`arrowMat s t w = [[t, wᵀ], [w, s I]]`, as the exact layer's (`Real.arrowMat`), in `𝕋`: the block of
the cone that forces `s ≥ 0` and, at `s = 0`, the point `w = 0`. Its entries are the arguments and
`zero`.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def arrowMat (s t : 𝕋) (w : Vec 𝕋 N) : Mat 𝕋 (N + 1) (N + 1) := fun p q =>
  Fin.cases (motive := fun _ => 𝕋) (Fin.cases (motive := fun _ => 𝕋) t w q)
    (fun i => Fin.cases (motive := fun _ => 𝕋) (w i) (fun j => if i = j then s else zero) q) p

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
