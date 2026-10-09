import CORALean.Global.Tensor
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The arrowhead matrix

`arrowMat s t w = [[t, wᵀ], [w, s I]]`, of size `N + 1`: the block of the cone of a spectrahedral
shadow that forces `s ≥ 0` and, when `s = 0`, the point `w = 0`. It is linear in `(s, t, w)`;
`SpectraShadow.cone` combines it with the shadow's own inequality. CORA writes the same condition as
one `2 × 2` block `[[s, wᵢ], [wᵢ, t]] ⪰ 0` per coordinate.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Matrix CORALean

variable {N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def arrowMat (s t : ℝ) (w : Vec ℝ N) : Mat ℝ (N + 1) (N + 1) :=
  Matrix.of fun p q =>
    Fin.cases (motive := fun _ => ℝ) (Fin.cases (motive := fun _ => ℝ) t w q)
      (fun i => Fin.cases (motive := fun _ => ℝ) (w i) (fun j => if i = j then s else 0) q) p

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
