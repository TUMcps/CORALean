module

public import CORALean.ContSet.Interval.Float.Operations.MaterialiseMat
public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# `Zonotope.materialiseMat`

## Inputs
* `Z` – matrix zonotope

## Output
* matrix zonotope with center, generators and box stored
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}
variable {m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The same storage at `Mat 𝕋 m n`, the matrix zonotope: center, every generator and the
interval-matrix box. `matPow` and the Taylor sum apply it at each step. -/
def Zonotope.materialiseMat (Z : Zonotope (Mat 𝕋 m n)) : Zonotope (Mat 𝕋 m n) :=
  let c : Vector (Vector 𝕋 n) m := Vector.ofFn fun i => Vector.ofFn (Z.c i)
  let G : Vector (Vector (Vector 𝕋 n) m) Z.h :=
    Vector.ofFn fun k => Vector.ofFn fun i => Vector.ofFn (Z.G k i)
  { h := Z.h
    c := fun i j => (c[i.val]'i.isLt)[j.val]'j.isLt
    G := fun k i j => ((G[k.val]'k.isLt)[i.val]'i.isLt)[j.val]'j.isLt
    I_error := Z.I_error.materialiseMat }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
