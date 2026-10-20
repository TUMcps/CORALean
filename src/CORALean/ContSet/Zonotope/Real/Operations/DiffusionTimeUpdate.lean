module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# `Zonotope.diffusionTimeUpdate`

The time update, Step 3 of [1, Alg. 1]: the diffused zonotope `⟨ć, G̃⟩` is carried through the
dynamics and the process noise `⟨0, Q⟩` is added, `ĉ = F ć` and `Ĝ = [F G̃, Q]`. It is the predicted
set `F Ẑ ⊕ Z_Q` of [1, Def. 2], Eq. 9, up to the `+ 0` the sum puts on the center. `Q` is the matrix
of the generator columns of `Z_Q = ⟨0, Q⟩`.

## Inputs
* `F` – dynamics matrix
* `Q` – process-noise generators
* `Zt` – diffused zonotope

## Output
* zonotope carried through the dynamics plus noise

## References

* [1] A. Alanwar, J. J. Rath, H. Said, K. H. Johansson and M. Althoff. "Distributed Set-Based
      Observers Using Diffusion Strategies". Journal of the Franklin Institute,
      360(10):6976-6993, 2023. arXiv:2003.10347.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n nq : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.diffusionTimeUpdate (F : Mat ℝ n n) (Q : Mat ℝ n nq) (Zt : Zonotope (Vec ℝ n)) :
    Zonotope (Vec ℝ n) :=
  let ĉ : Vec ℝ n := F *ᵥ Zt.c                                                -- ĉ = F ć
  let Ĝ : Fin (Zt.h + nq) → Vec ℝ n :=                                         -- Ĝ = [F G̃, Q]
    Fin.append (fun j => F *ᵥ Zt.G j) (fun j i => Q i j)
  { h := Zt.h + nq, c := ĉ, G := Ĝ }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
