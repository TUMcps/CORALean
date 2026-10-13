import CORALean.ContSet.Zonotope.Real.Zonotope
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Sublists
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# `Zonotope.methodCBasis`: method C's choice of `Γ`

[1, Sec. 5.4.2]'s method C, the generator selection of its Sec. 5.3.2 it recommends for
[1, Prop. 8]: keep the `p̃ = n + κ` longest generators; rank every `n` of them by
`Θ̃ = |det[g^(i₁), ..., g^(iₙ)]|⁻¹`; keep the best `λ = n + κ̃`; of those, take the one whose
parallelotope has the least volume `Θ* = V(Γ box(Γ⁻¹Z))`. The paper fixes `κ = 8`, `κ̃ = 3`.

Ranked by `|det|` descending rather than by `Θ̃` ascending, the same order where `det ≠ 0`,
and where `det = 0` Lean's `0⁻¹ = 0` would rank first what the paper ranks last; singular
choices are dropped outright, being no full-rank `Γ`. `Θ*` is the parallelotope's volume
in closed form, `|det Γ| ∏ᵢ 2 Σⱼ |(Γ⁻¹g^(j))ᵢ|`. With nothing left, `Γ = I`: a box.

Combinations are `List.sublistsLen`, so each subset is ranked once, in one order.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Computing Reachable Sets of Hybrid
      Systems Using a Combination of Zonotopes and Polytopes". Nonlinear
      Analysis: Hybrid Systems, 4(2):233-249, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. 5.4.2]'s method C: the `Γ` of the least-volume parallelotope among the `n + κ̃`
largest-volume choices of `n` of the `n + κ` longest generators, or `I` if none is regular. -/
noncomputable def Zonotope.methodCBasis (Z : Zonotope (Vec ℝ n)) (κ κ' : ℕ) : Mat ℝ n n :=
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

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
