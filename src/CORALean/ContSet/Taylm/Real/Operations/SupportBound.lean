module

public import CORALean.ContSet.Taylm.Real.Operations.Bounds
public import CORALean.ContSet.Taylm.Real.Operations.Basic
public import CORALean.ContSet.Taylm.Real.Theorems.BoundsMem
public import CORALean.ContSet.Taylm.Real.Theorems.MemConstructIff
public import CORALean.ContSet.Taylm.Real.Theorems.Basic
public import CORALean.Global.SupportFunction.SupportFunction
public import Mathlib.Algebra.BigOperators.Pi

@[expose] public section

/-!
# `Taylm.supportBound`

CORA's `@taylm/supportFunc_` at its `upper` type: `I = interval(dir' * tay)` and the value is
the interval's supremum. The row `dir' * tay` is `Taylm.mtimes` at a one-row matrix, its range
is `Taylm.bounds`, and the supremum is that range's upper end. An upper bound only: the range of
a Taylor model's polynomial is enclosed, not attained. CORA's other types are not given (only
`lower` and `range` are, its `else` branch being empty).

## Inputs
* `c` – direction as a linear functional
* `T` – family of Taylor models

## Output
* upper bound of the functional on the set
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The direction `c` as a coefficient vector: its value at each unit vector. -/
theorem Taylm.aux_linearMap_eq_sum (c : Vec ℝ m →ₗ[ℝ] ℝ) (x : Vec ℝ m) : -- --- CONCL ---
    c x = ∑ j, c (Pi.single j 1) * x j := by -- --- PROOF ---
  conv_lhs => rw [pi_eq_sum_univ x]
  simp only [map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]
  congr 2
  ext k
  simp [Pi.single_apply, eq_comm]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `supportFunc_`, `upper`: the upper end of the range of `dirᵀ T`. -/
noncomputable def Taylm.supportBound (c : Vec ℝ m →ₗ[ℝ] ℝ) (T : Fin m → Taylm n) :
    SupportBound (Taylm.construct T) c where
  val := (Taylm.mtimes (fun (_ : Fin 1) j => c (Pi.single j 1)) T 0).bounds.sup
  le x hx := by
    -- the point is the value at some `t` of functions the models enclose
    obtain ⟨f, hf, t, ht, hxf⟩ := (Taylm.mem_construct_iff T x).1 hx
    have hmem := Taylm.bounds_mem
      (Taylm.mtimes_outer (fun (_ : Fin 1) j => c (Pi.single j 1)) hf 0) ht
    rw [Taylm.aux_linearMap_eq_sum c x]
    simpa [hxf] using hmem.2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
