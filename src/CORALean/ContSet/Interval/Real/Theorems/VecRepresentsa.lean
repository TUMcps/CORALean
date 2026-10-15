module

public import CORALean.ContSet.Interval.Real.Operations.Vec
public import CORALean.ContSet.Interval.Real.Operations.RepresentsaEmptySet
public import CORALean.ContSet.Interval.Real.Operations.RepresentsaPoint
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Operations.IsNonempty

@[expose] public section

/-!
# `representsa` of an interval matrix is that of its vectorisation

CORA's `intervalMatrix/representsa` hands `reshape(interval(intMat), [], 1)` to the vector
interval, so whatever the vector class answers is the answer. The library's three tests
(`representsa_emptySet`, `representsa_origin`, `representsa_point`) are the same on the stacked
bounds as on the matrices, entry for entry; they are generic over the ambient type and already
hold at `Mat ℝ m n` directly. The other types CORA's `representsa` accepts (zonotope, hyperplane,
...) are not modelled for the interval class, so not here either.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The stacked lower bound at the position of `(i, j)`. -/
theorem aux_vec_inf (A : Interval (Mat ℝ m n)) (i : Fin m) (j : Fin n) :
    A.vec.inf (finProdFinEquiv (j, i)) = A.inf i j := by
  simp only [Interval.vec, Equiv.symm_apply_apply]

/-- The stacked upper bound at the position of `(i, j)`. -/
theorem aux_vec_sup (A : Interval (Mat ℝ m n)) (i : Fin m) (j : Fin n) :
    A.vec.sup (finProdFinEquiv (j, i)) = A.sup i j := by
  simp only [Interval.vec, Equiv.symm_apply_apply]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Stacking the entries does not change whether the box is empty, the origin or a point. -/
theorem Interval.vec_representsa (A : Interval (Mat ℝ m n)) :
    (A.vec.representsa_emptySet ↔ A.representsa_emptySet) ∧
    (A.vec.representsa_origin ↔ A.representsa_origin) ∧
    (A.vec.representsa_point ↔ A.representsa_point) := by -- --- PROOF ---
  refine ⟨?_, ?_, ?_⟩
  · -- emptiness: crossed bounds at some position
    unfold Interval.representsa_emptySet Interval.IsNonempty
    refine not_congr ⟨fun h p => ?_, fun h k => ?_⟩
    · have := h (finProdFinEquiv (p.2, p.1))
      change A.vec.inf (finProdFinEquiv (p.2, p.1)) ≤ A.vec.sup (finProdFinEquiv (p.2, p.1))
        at this
      rw [aux_vec_inf, aux_vec_sup] at this
      exact this
    · obtain ⟨⟨j, i⟩, rfl⟩ := finProdFinEquiv.surjective k
      have : A.inf i j ≤ A.sup i j := h (i, j)
      show A.vec.inf (finProdFinEquiv (j, i)) ≤ A.vec.sup (finProdFinEquiv (j, i))
      rw [aux_vec_inf, aux_vec_sup]
      exact this
  · -- the origin: both bounds zero
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨funext fun i => funext fun j => ?_, funext fun i => funext fun j => ?_⟩
      · simpa [aux_vec_inf] using congrFun h1 (finProdFinEquiv (j, i))
      · simpa [aux_vec_sup] using congrFun h2 (finProdFinEquiv (j, i))
    · rintro ⟨h1, h2⟩
      refine ⟨funext fun k => ?_, funext fun k => ?_⟩
      · obtain ⟨⟨j, i⟩, rfl⟩ := finProdFinEquiv.surjective k
        simp [aux_vec_inf, h1]
      · obtain ⟨⟨j, i⟩, rfl⟩ := finProdFinEquiv.surjective k
        simp [aux_vec_sup, h2]
  · -- a point: the two bounds equal
    constructor
    · intro h
      refine funext fun i => funext fun j => ?_
      have := congrFun h (finProdFinEquiv (j, i))
      rwa [aux_vec_inf, aux_vec_sup] at this
    · intro h
      refine funext fun k => ?_
      obtain ⟨⟨j, i⟩, rfl⟩ := finProdFinEquiv.surjective k
      rw [aux_vec_inf, aux_vec_sup]
      exact congrFun (congrFun h i) j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
