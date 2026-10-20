module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.Tensor
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# `Zonotope.quadMapTri`

[1, Lemma 1 (generators)] with its generators as printed: the center
`dᵢ = cᵀQ⁽ⁱ⁾c + 0.5 Σₛ g⁽ˢ⁾ᵀQ⁽ⁱ⁾g⁽ˢ⁾`, the `p` linear generators `h⁽ʲ⁾ᵢ = cᵀQ⁽ⁱ⁾g⁽ʲ⁾ + g⁽ʲ⁾ᵀQ⁽ⁱ⁾c`,
the `p` squares `h⁽ᵖ⁺ʲ⁾ᵢ = 0.5 g⁽ʲ⁾ᵀQ⁽ⁱ⁾g⁽ʲ⁾`, and one generator
`h⁽²ᵖ⁺ˡ⁾ᵢ = g⁽ʲ⁾ᵀQ⁽ⁱ⁾g⁽ᵏ⁾ + g⁽ᵏ⁾ᵀQ⁽ⁱ⁾g⁽ʲ⁾` for each pair `j < k` alone, numbered by
`aux_quadMapPairIdx`. That is `σ = C(p + 2, 2) - 1` generators. `Zonotope.quadMap` indexes the pair
block by all of `Fin p × Fin p`, zero off `j < k`.

## Inputs
* `Q` – family of quadratic matrices
* `Z` – zonotope

## Output
* enclosing zonotope with fewer pair generators

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The pairs `j < k` of `Fin p`, as `p(p - 1)/2 = C(p, 2)` of them. -/
theorem Zonotope.aux_card_ltPair (p : ℕ) : -- --- CONCL ---
    Fintype.card {jk : Fin p × Fin p // jk.1 < jk.2} = p.choose 2 := by -- --- PROOF ---
  -- a pair is its larger index `k` and some `j : Fin k`
  let e : {jk : Fin p × Fin p // jk.1 < jk.2} ≃ Σ k : Fin p, Fin k :=
    { toFun := fun jk => ⟨jk.1.2, ⟨jk.1.1, jk.2⟩⟩
      invFun := fun kj => ⟨(⟨kj.2, kj.2.2.trans kj.1.2⟩, kj.1), kj.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun k => k) p, Nat.choose_two_right,
    ← Finset.sum_range_id_mul_two p, Nat.mul_div_cancel _ Nat.two_pos]

/-- [1, Lemma 1 (generators)]: the index `l` of the pair generators, against the pairs `j < k`. -/
noncomputable def Zonotope.aux_quadMapPairIdx (p : ℕ) :
    Fin (p.choose 2) ≃ {jk : Fin p × Fin p // jk.1 < jk.2} :=
  (Fintype.equivFinOfCardEq (Zonotope.aux_card_ltPair p)).symm


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Lemma 1 (generators)]: the enclosing zonotope, the pair block over `j < k` only. -/
noncomputable def Zonotope.quadMapTri (Q : Fin m → Mat ℝ n n) (Z : Zonotope (Vec ℝ n)) :
    Zonotope (Vec ℝ m) where
  h := Z.h + Z.h + Z.h.choose 2
  c := fun i => Z.c ⬝ᵥ (Q i *ᵥ Z.c) + (1 / 2) * ∑ s, Z.G s ⬝ᵥ (Q i *ᵥ Z.G s)
  G := Fin.append
    (Fin.append
      (fun j i => Z.c ⬝ᵥ (Q i *ᵥ Z.G j) + Z.G j ⬝ᵥ (Q i *ᵥ Z.c))
      (fun j i => (1 / 2) * Z.G j ⬝ᵥ (Q i *ᵥ Z.G j)))
    (fun l i =>
      let jk := (Zonotope.aux_quadMapPairIdx Z.h l).1
      Z.G jk.1 ⬝ᵥ (Q i *ᵥ Z.G jk.2) + Z.G jk.2 ⬝ᵥ (Q i *ᵥ Z.G jk.1))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
