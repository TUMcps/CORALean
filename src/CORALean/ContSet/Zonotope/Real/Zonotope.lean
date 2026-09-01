import CORALean.ContSet.Interval.Real.API

/-!
# Zonotopes: the representation

CORA's `zonotope`, with the same centre `c` and generator matrix `G`, denoting
every point the generators reach from `c` with coefficients in `[-1, 1]`.

Over any real module, not just `Vec ℝ n`: nothing about a centre plus a bounded
combination of generators mentions coordinates. So `Zonotope (Mat ℝ n m)` is
CORA's `matZonotope` and needs no separate development.

Generators are a family rather than a matrix, a matrix being available only when
the ambient type has coordinates. At `Vec ℝ n` the two differ by transposition:
`G j i` is coordinate `i` of generator `j`.

The generator count is a field, not a type index: operations grow it freely and
`reduce` is what bounds it, where the algorithm asks rather than everywhere.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   01-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

structure Zonotope (α : Type) where
  h : ℕ
  c : α
  G : Fin h → α

def Zonotope.construct (Z : Zonotope α) : Set α :=
  {x | ∃ β : Fin Z.h → ℝ, (∀ j, |β j| ≤ 1) ∧ x = Z.c + ∑ j, β j • Z.G j}

/-- The same membership read coordinatewise, which is the form the operations
that need coordinates are stated in. -/
theorem Zonotope.mem_construct_iff {n : ℕ} {Z : Zonotope (Vec ℝ n)} {x : Vec ℝ n} :
    x ∈ Z.construct ↔
      ∃ β : Fin Z.h → ℝ, (∀ j, |β j| ≤ 1) ∧ ∀ i, x i = Z.c i + ∑ j, Z.G j i * β j := by
  constructor
  · rintro ⟨β, hβ, rfl⟩
    refine ⟨β, hβ, fun i => ?_⟩
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact congrArg _ (Finset.sum_congr rfl fun j _ => mul_comm _ _)
  · rintro ⟨β, hβ, hx⟩
    refine ⟨β, hβ, funext fun i => ?_⟩
    rw [hx i]
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact congrArg _ (Finset.sum_congr rfl fun j _ => mul_comm _ _)

end CORALean.Real
