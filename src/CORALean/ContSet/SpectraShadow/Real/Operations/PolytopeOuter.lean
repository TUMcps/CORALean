module

public import CORALean.ContSet.SpectraShadow.Real.Operations.SupportFunc
public import CORALean.ContSet.SpectraShadow.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Operations.EmptySet

@[expose] public section

/-!
# `SpectraShadow.polytopeOuter`

CORA's `polytope(SpS, 'outer', splits)` (`@spectraShadow/polytope.m`), in one to three dimensions:
the shadow shifted by its `center`, its support along a grid of directions `dirs`
(`aux_getDirections`: the two directions of a line, the circle at `splits` angles, or the points of
Leopardi's `eq_point_set` on the sphere), the rows `dirᵀ x ≤ val` for the directions with a finite
support value `val`, and the polytope shifted back. An empty shadow gives the empty polytope.
`center` is whichever feasible point the solver reports, so it is an argument `c`; the rows do not
depend on it (`Theorems.PolytopeOuter` holds for every `c`). The grid is any family of functionals.
An empty list of rows is the whole space, as CORA's `polytope.Inf`.

## Inputs
* `S` – spectrahedral shadow
* `c` – center of length `n`
* `dirs` – family indexed by `Fin N`

## Output
* the rows `dirᵀ x ≤ support` along `dirs` of the shadow shifted by `c`, shifted back
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Classical

variable {n N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def SpectraShadow.polytopeOuter (S : SpectraShadow (Vec ℝ n)) (c : Vec ℝ n)
    (dirs : Fin N → (Vec ℝ n →ₗ[ℝ] ℝ)) : HPolytope (Vec ℝ n) :=
  if S.construct = ∅ then HPolytope.emptySet (Vec ℝ n) else
  let SpS : SpectraShadow (Vec ℝ n) := S.translate (-c)
  let val : Fin N → EReal := fun i => SpS.supportFunc (dirs i)
  let finite : List (Fin N) := (List.finRange N).filter fun i => val i ≠ ⊤ ∧ val i ≠ ⊥
  let P_A : Fin finite.length → (Vec ℝ n →ₗ[ℝ] ℝ) := fun r => dirs (finite.get r)
  let P_b : Fin finite.length → ℝ := fun r => (val (finite.get r)).toReal
  { m := finite.length, A := P_A, b := fun r => P_b r + P_A r c, me := 0, Ae := Fin.elim0,
    be := Fin.elim0 }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
