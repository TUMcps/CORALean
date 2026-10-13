module

public import CORALean.ContSet.Interval.Real.Definitions.BoxPlane
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Fin

@[expose] public section

/-!
# An s-face with `j` defined labels holds `2^(n-j)` vertices

[1, Def. 3]: if `s = (b₁, …, b_j, *, …, *)`, the cardinality of `V(s)` is `|V(s)| = 2^(n-j)`:
a vertex of the face is a free choice of the `n - j` undefined labels.

## References

* [1] C. Lara, J. J. Flores and F. Calderon. "On the Hyperbox – Hyperplane Intersection
      Problem". INFOCOMP Journal of Computer Science, 8(4):21-27, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

open Classical in
theorem Interval.card_prefixFace {j : ℕ} (hj : j ≤ n) (p : Fin n → Bool) :
    Fintype.card {l : Fin n → Bool // l ∈ Interval.prefixFace j p} =
      2 ^ (n - j) := by -- --- PROOF ---
  -- a vertex of the face is its labels at the undefined positions
  let e : {l : Fin n → Bool // l ∈ Interval.prefixFace j p} ≃
      ({i : Fin n // ¬ (i : ℕ) < j} → Bool) :=
    { toFun := fun l i => l.1 i.1
      invFun := fun g => ⟨fun i => if h : (i : ℕ) < j then p i else g ⟨i, h⟩,
        fun i hi => by simp [hi]⟩
      left_inv := fun l => by
        apply Subtype.ext
        funext i
        by_cases hi : (i : ℕ) < j
        · simp [hi, l.2 i hi]
        · simp [hi]
      right_inv := fun g => by
        funext i
        simp [i.2] }
  rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype]
  -- the undefined positions are `j, …, n - 1`
  congr 1
  have h1 := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun i : Fin n => (i : ℕ) < j)
  rw [Fin.card_filter_val_lt, Finset.card_univ, Fintype.card_fin, min_eq_right hj] at h1
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
