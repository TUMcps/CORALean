module

public import CORALean.Global.Float.Sqrt

@[expose] public section

/-!
# How far the scaled first basis vector is from the start vector, in floats

The first Arnoldi vector is `c / ν` rounded, so `ν v(1)` is not `c`: the error
`e^{tA}(c - ν v(1))`, the start term beside the Krylov error of [1, Thm. 3], is at most
`e^{tμ}‖c - ν v(1)‖₂`. Entry `r` of `c - ν v(1)_r` lies between `lo = c_r - ν v(1)_r` with the
product rounded up and `hi` with it rounded down; the norm is `normUp` of the larger magnitude.

## Inputs
* `p` – Newton steps per norm
* `c` – start vector
* `ν` – scale
* `v` – first basis vector

## Output
* upper bound of the Euclidean norm of the difference

## References

* [1] [T. Jawecki, W. Auzinger and O. Koch. "Computable upper error bounds for Krylov approximations
      to matrix exponentials and associated φ-functions". BIT Numerical Mathematics,
      2020.](../../../../../../references/2020/jawecki-bit-krylov-error-bounds.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `‖c - ν v‖₂` from above, entry by entry between `subDown c (ν v)↑` and `subUp c (ν v)↓`. -/
def Krylov.startErrorFloat (p : ℕ) (c : Vec 𝕋 n) (ν : 𝕋) (v : Vector 𝕋 n) : 𝕋 :=
  normUp p fun r : Fin n =>
    maximum (absolute (subDown (c r) (mulUp ν v[r]))) (absolute (subUp (c r) (mulDown ν v[r])))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
