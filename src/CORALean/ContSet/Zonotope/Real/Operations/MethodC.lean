module

public import CORALean.ContSet.Zonotope.Real.Operations.Parallelotope
public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.List.MinMax
public import Mathlib.Data.List.Sort
public import Mathlib.Data.List.Sublists
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# `Zonotope.methodC`: a zonotope reduced to a parallelotope by method C

[1, Sec. 5.4.2]'s method C, the reduction to a parallelotope the paper recommends for the
halfspace conversion: [1, Prop. 8]'s `Γ box(Γ⁻¹Z)` at the `Γ` `aux_methodCBasis` selects,
`κ = 8`, `κ̃ = 3` in the paper's evaluation and `κ = 5` in its numerical example.

CORA's `reduce(Z, 'methC', o)`, `Zonotope.reduceMethC`, is a relative: it boxes only what
Girard's ranking drops, keeps `λ = 1`, and ranks lengths after its own row scaling.

## Inputs
* `Z` – zonotope
* `κ` – length-filter size
* `κ'` – volume-filter size

## Output
* parallelotope enclosing `Z`

## References

* [1] [M. Althoff, O. Stursberg and M. Buss. "Computing Reachable Sets of Hybrid Systems Using a
      Combination of Zonotopes and Polytopes". Nonlinear Analysis: Hybrid Systems,
      2010.](../../../../../../references/2010/althoff-nahs-zonotopes-polytopes.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}
open Matrix


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- [1, Sec. 5.4.2]'s method C: the `Γ` of the least-volume parallelotope among the `n + κ̃`
largest-volume choices of `n` of the `n + κ` longest generators, or `I` if none is regular. -/
noncomputable def Zonotope.aux_methodCBasis (Z : Zonotope (Vec ℝ n)) (κ κ' : ℕ) : Mat ℝ n n :=
  let p := min (n + κ) Z.h
  -- the `p̃` longest generators by `‖g‖₂`, longest first
  let len : Fin Z.h → ℝ := fun j => ∑ i, Z.G j i ^ 2
  let longest : Fin p → Fin Z.h :=
    fun k => Tuple.sort (fun j => -len j) (Fin.castLE (min_le_right _ _) k)
  -- every `n` of them, and the matrix `Γ` their generators make
  let combos : List (List (Fin p)) := List.sublistsLen n (List.finRange p)
  let Γ : List (Fin p) → Mat ℝ n n := fun l => Matrix.of fun i k =>
    match l[(k : ℕ)]? with
    | some j => Z.G (longest j) i
    | none => 0
  -- the `λ = n + κ̃` best by `Θ̃ = |det|⁻¹`, singular choices dropped
  let regular := combos.filter fun l => (Γ l).det ≠ 0
  let best := (regular.mergeSort fun a b => decide (|(Γ b).det| ≤ |(Γ a).det|)).take (n + κ')
  -- of those, the least `Θ* = V(Γ box(Γ⁻¹Z))`
  let Θstar : List (Fin p) → ℝ := fun l =>
    |(Γ l).det| * ∏ i, 2 * ∑ j, |((Γ l)⁻¹ *ᵥ Z.G j) i|
  match best.argmin Θstar with
  | some l => Γ l
  | none => 1


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. 5.4.2]: the parallelotope method C encloses `Z` by. -/
noncomputable def Zonotope.methodC (Z : Zonotope (Vec ℝ n)) (κ κ' : ℕ) : Zonotope (Vec ℝ n) :=
  Z.parallelotope (Z.aux_methodCBasis κ κ')

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
