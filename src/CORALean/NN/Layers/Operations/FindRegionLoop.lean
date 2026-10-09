import CORALean.NN.Layers.Operations.FindRegionLeft
import CORALean.NN.Layers.Operations.FindRegionRight

/-!
# The main loop of `findRegionPolys`
`while l < u` of CORA's: a left polynomial from `l`, then, unless that reached `u`, a right
polynomial from `u`, moving `l` and `u` inward. The loop ends when `u ≤ l` is certified by
`le`; CORA's `l == u` break after the left polynomial is the same test. `fuel` bounds the outer
loop and each inner halving, `none` being `CORA:notConverged` or running out of it. The
regions come back in the order found, not sorted by `l` as CORA's last line does.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The regions found between `l` and `u`, put in front of `acc`. -/
def findRegionLoop (F : (o : ℕ) → PolyRelaxation 𝕋 o) (order : ℕ) (tol : 𝕋) :
    ℕ → 𝕋 → 𝕋 → List (RegionPoly 𝕋) → Option (List (RegionPoly 𝕋))
  | 0, l, u, acc => if le u l then some acc else none
  | fuel + 1, l, u, acc =>
    if le u l then some acc
    else
      match findRegionLeft F order tol l (fuel + 1) u with
      | none => none
      | some (rL, l') =>
        if le u l' then some (rL :: acc)
        else
          match findRegionRight F order tol u (fuel + 1) l' with
          | none => none
          | some (rR, u') => findRegionLoop F order tol fuel l' u' (rR :: rL :: acc)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
