module

public import CORALean.ContSet.Zoo.Real.Zoo
public import CORALean.ContSet.Conversion.Real.Operations.Basic

@[expose] public section

/-!
# `Zoo.ofInterval`

CORA's constructor `zoo(int, methods, names, max_order, ...)`, `@zoo/zoo.m`: for an interval domain
`int` it builds, for each requested method, an object that stands for the domain's variables,
`taylm(int, max_order, ...)` for `taylm(int)`, `affine(int, ...)` (a Taylor model of order `1`)
for `affine(int)`, and `int` itself for `interval`. Here the `i`-th coordinate, with the two
members a `Zoo` has: the Taylor model at order `N` (`Interval.taylm`) and the interval
`[inf i, sup i]`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Zoo.ofInterval (I : Interval (Vec ℝ n)) (N : ℕ) (i : Fin n) : Zoo n :=
  ⟨some (I.taylm N i), some ⟨fun _ => I.inf i, fun _ => I.sup i⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
