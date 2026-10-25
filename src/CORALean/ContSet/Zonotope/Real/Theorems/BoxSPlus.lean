module

public import CORALean.ContSet.Zonotope.Real.Operations.BoxS
public import CORALean.ContSet.Zonotope.Real.Operations.Plus
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# `Box_S` of a zonotope sum has the summed bounds

[1, Sec. 4.2]: `Box_S(Z₁ ⊕ Z₂) = Box_S(Z₁) ⊕ Box_S(Z₂)`, the right side the band of the
summed bounds `[m₁ + m₂, M₁ + M₂]_S`, which is how [1] adds two `S`-band intersections.
Each bound of `Box_S(Z₁ ⊕ Z₂)` sums over the concatenated generators, and so splits into
the two zonotopes' bounds. That the band of the summed bounds is the Minkowski sum of the
two bands is false (`ContSet.exists_hyperplanePolyhedron_add_ne`); it contains it
(`ContSet.hyperplanePolyhedron_add_subset`).

## Inputs
* `Z₁` – first zonotope
* `Z₂` – second zonotope
* `S` – finite set of directions

## Hypotheses
* none

## Conclusion
* the box of a sum is the sum of the bounds

## References

* [1] A. Girard, C. Le Guernic and O. Maler. "Efficient Computation of Reachable Sets of Linear
      Time-Invariant Systems with Inputs". Hybrid Systems: Computation and Control, 2006.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 4.2]: `Box_S(Z₁ ⊕ Z₂) = [m₁ + m₂, M₁ + M₂]_S`. -/
theorem Zonotope.boxS_plus (Z₁ Z₂ : Zonotope (Vec ℝ n)) (S : Finset (Vec ℝ n)) : -- --- CONCL ---
    (Z₁.plus Z₂).boxS S = ContSet.hyperplanePolyhedron S
      ((fun s => Z₁.c ⬝ᵥ s - ∑ j, |Z₁.G j ⬝ᵥ s|) + fun s => Z₂.c ⬝ᵥ s - ∑ j, |Z₂.G j ⬝ᵥ s|)
      ((fun s => Z₁.c ⬝ᵥ s + ∑ j, |Z₁.G j ⬝ᵥ s|) +
        fun s => Z₂.c ⬝ᵥ s + ∑ j, |Z₂.G j ⬝ᵥ s|) := by -- --- PROOF ---
  -- the generator sum splits at the concatenation, stated at `plus`'s own count
  have hs : ∀ s : Vec ℝ n, ∑ j : Fin (Z₁.plus Z₂).h, |(Z₁.plus Z₂).G j ⬝ᵥ s|
      = ∑ j, |Z₁.G j ⬝ᵥ s| + ∑ j, |Z₂.G j ⬝ᵥ s| := fun s => by
    have h := Fin.sum_univ_add fun j : Fin (Z₁.h + Z₂.h) => |Fin.append Z₁.G Z₂.G j ⬝ᵥ s|
    simp only [Fin.append_left, Fin.append_right] at h
    exact h
  have hc : ∀ s : Vec ℝ n, (Z₁.plus Z₂).c ⬝ᵥ s = Z₁.c ⬝ᵥ s + Z₂.c ⬝ᵥ s := fun s =>
    add_dotProduct _ _ _
  simp only [Zonotope.boxS, hs, hc]
  congr 1 <;> funext s <;> simp only [Pi.add_apply] <;> ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
