module

public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Taylm.Float.Taylm
public import CORALean.ContSet.Taylm.Real.Theorems.Basic
public import CORALean.ContSet.Taylm.Real.Theorems.MonomialSingle
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfAppend
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import Mathlib.Algebra.BigOperators.Pi

@[expose] public section

/-!
# A polynomial zonotope as an array of Taylor models, over a floating-point scalar

`PolyZonotope.taylm` is the construction; `PolyZonotope_to_Taylm` states and proves what it
guarantees.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.taylm (pZ : PolyZonotope (Vec 𝕋 n)) (N : ℕ) : Fin n → Taylm 𝕋 (pZ.p + pZ.q) :=
  fun i => ⟨(pZ.c i, 0) :: (List.ofFn (fun j => (pZ.G j i, Fin.append (fun k => pZ.E k j) 0))
    ++ List.ofFn (fun l => (pZ.GI l i, Pi.single (Fin.natAdd pZ.p l) 1))),
    pZ.I_error.inf i, pZ.I_error.sup i, N⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
