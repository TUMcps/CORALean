import CORALean.ContSet.Zonotope.Float.Operations.ErrUp
import CORALean.ContSet.Zonotope.Float.Operations.ReduceGirardBox

/-!
# `Zonotope.reduceBoxError`, the error of a reduction in floats

`Real.Zonotope.reduceBoxError` computed in `𝕋`: [1]'s `ε_S([t_i, t_{i+1}])`, `err(·)` at the
box a reduction to order `o` absorbs the dropped generators into. `reduceGirardBox` is that
box, and `errUp` bounds its Euclidean `err` from above, so a float `ε^r_k` is never smaller
than the exact one it stands for.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `err` at the box a reduction to order `o` absorbs the dropped generators into, from above. -/
def Zonotope.reduceBoxError (Z : Zonotope 𝕋 n) (o : ℕ) : 𝕋 :=
  (Z.reduceGirardBox o).errUp

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
