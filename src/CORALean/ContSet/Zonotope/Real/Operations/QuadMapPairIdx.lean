module

public import CORALean.Global.Tensor
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# `Zonotope.quadMapPairIdx`

[1, Lemma 1 (generators)] numbers the pair generators `h^(2p+l)` by `l`, one for every pair `j < k`
of the `p` generators of `Z`: `C(p, 2)` of them. This is that numbering, `Fin (C(p, 2))` against the
pairs `{(j, k) | j < k}`. Which pair gets which `l` the lemma leaves open, and no statement depends
on it.

The count is `Σ_{k < p} k = p(p - 1)/2`: a pair is its larger index `k` and a `j < k`.

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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The pairs `j < k` of `Fin p`, as `p(p - 1)/2 = C(p, 2)` of them. -/
theorem Zonotope.aux_card_ltPair (p : ℕ) :
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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Lemma 1 (generators)]: the index `l` of the pair generators, against the pairs `j < k`. -/
noncomputable def Zonotope.quadMapPairIdx (p : ℕ) :
    Fin (p.choose 2) ≃ {jk : Fin p × Fin p // jk.1 < jk.2} :=
  (Fintype.equivFinOfCardEq (Zonotope.aux_card_ltPair p)).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
