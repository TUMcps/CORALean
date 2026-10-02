import Mathlib.Analysis.RCLike.Lemmas
import CORALean.Global.Tensor

/-!
# Where a linear form is positive on a pointed cone

What [1, Thm. 2] needs and no facet enumeration supplies: if `w` pairs
positively with some `z` of the cone `{y | ∀ j, a⁽ʲ⁾ ⬝ᵥ y ≥ 0}`, then it does so
at a `y` that `N - 1` linearly independent constraints already hold — an edge of
the cone, which is what a facet normal of a zonotope is.

The proof pivots. While fewer than `N - 1` independent constraints are active,
a direction `u` annihilates all of them and `w` besides; `u` or `-u` leaves the
cone, only `0` annihilating every `a⁽ʲ⁾`, and walking that way to where the
first constraint bites leaves `w ⬝ᵥ ·` positive and makes one more constraint
active — independent of those already there, since `u` does not annihilate it.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Module

variable {N : ℕ} {ι : Type} [Fintype ι]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Pairing with `u`, as a linear functional of the left argument. -/
def aux_dotL (u : Vec ℝ N) : Vec ℝ N →ₗ[ℝ] ℝ where
  toFun v := v ⬝ᵥ u
  map_add' v w := add_dotProduct v w u
  map_smul' r v := smul_dotProduct r v u

/-- Fewer than `N` constraints leave a direction annihilating every one. -/
theorem aux_exists_annihilator {k : ℕ} (b : Fin k → Vec ℝ N) (hk : k < N) :
    ∃ u : Vec ℝ N, u ≠ 0 ∧ ∀ i, b i ⬝ᵥ u = 0 := by -- --- PROOF ---
  have hsrc : finrank ℝ (Vec ℝ N) = N := by
    show finrank ℝ (Fin N → ℝ) = N
    simp
  have htgt : finrank ℝ (Fin k → ℝ) = k := by simp
  have hlt : finrank ℝ (Fin k → ℝ) < finrank ℝ (Vec ℝ N) := by rw [hsrc, htgt]; exact hk
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp
    (LinearMap.ker_ne_bot_of_finrank_lt (f := LinearMap.pi fun i => aux_dotL (b i)) hlt)
  refine ⟨u, hu0, fun i => ?_⟩
  have h : u ⬝ᵥ b i = 0 := by
    simpa [aux_dotL] using congrFun (LinearMap.mem_ker.mp hu) i
  rw [dotProduct_comm]
  exact h

/-- The pivot, repeated: while fewer than `N - 1` independent constraints are
active, walk to where one more is, keeping `w ⬝ᵥ ·` positive. -/
theorem aux_coneWalk (a : ι → Vec ℝ N) (w : Vec ℝ N)
    (hpt : ∀ y : Vec ℝ N, (∀ j, a j ⬝ᵥ y = 0) → y = 0) :
    ∀ (m k : ℕ) (S : Fin k → ι) (z : Vec ℝ N), N ≤ m + k →
      LinearIndependent ℝ (fun i => a (S i)) → (∀ i, a (S i) ⬝ᵥ z = 0) →
      (∀ j, 0 ≤ a j ⬝ᵥ z) → 0 < w ⬝ᵥ z →
      ∃ (k' : ℕ) (S' : Fin k' → ι) (z' : Vec ℝ N), N ≤ k' + 1 ∧
        LinearIndependent ℝ (fun i => a (S' i)) ∧ (∀ i, a (S' i) ⬝ᵥ z' = 0) ∧
        (∀ j, 0 ≤ a j ⬝ᵥ z') ∧ 0 < w ⬝ᵥ z' := by -- --- PROOF ---
  classical
  intro m
  induction m with
  | zero =>
    intro k S z hN hind hSz hz hw
    exact ⟨k, S, z, by omega, hind, hSz, hz, hw⟩
  | succ m ih =>
    intro k S z hN hind hSz hz hw
    by_cases hstop : N ≤ k + 1
    · exact ⟨k, S, z, hstop, hind, hSz, hz, hw⟩
    push Not at hstop
    -- a direction annihilating `w` and every constraint already active
    obtain ⟨u, hu0, hub⟩ := aux_exists_annihilator (Fin.cons w fun i => a (S i)) hstop
    have huw : w ⬝ᵥ u = 0 := by simpa using hub 0
    have huS : ∀ i, a (S i) ⬝ᵥ u = 0 := fun i => by simpa using hub i.succ
    -- the cone is pointed, so one of `±u` leaves it
    obtain ⟨j₀, hj₀⟩ : ∃ j, a j ⬝ᵥ u ≠ 0 := by
      by_contra h
      push Not at h
      exact hu0 (hpt u h)
    obtain ⟨v, hvw, hvS, hvj₀⟩ :
        ∃ v : Vec ℝ N, w ⬝ᵥ v = 0 ∧ (∀ i, a (S i) ⬝ᵥ v = 0) ∧ a j₀ ⬝ᵥ v < 0 := by
      rcases lt_or_gt_of_ne hj₀ with h | h
      · exact ⟨u, huw, huS, h⟩
      · exact ⟨-u, by rw [dotProduct_neg, huw, neg_zero],
          fun i => by rw [dotProduct_neg, huS i, neg_zero], by rw [dotProduct_neg]; linarith⟩
    -- the constraints the walk can bite on, and the first of them to do so
    set B : Finset ι := Finset.univ.filter fun j => a j ⬝ᵥ v < 0 with hB
    have hmemB : ∀ j, j ∈ B ↔ a j ⬝ᵥ v < 0 := by intro j; simp [hB]
    obtain ⟨j₁, hj₁B, hj₁min⟩ :=
      B.exists_min_image (fun j => (a j ⬝ᵥ z) / ((a j ⬝ᵥ z) - (a j ⬝ᵥ v)))
        ⟨j₀, (hmemB j₀).mpr hvj₀⟩
    have hden : ∀ j ∈ B, 0 < (a j ⬝ᵥ z) - (a j ⬝ᵥ v) := fun j hj => by
      have := (hmemB j).mp hj
      linarith [hz j]
    set t : ℝ := (a j₁ ⬝ᵥ z) / ((a j₁ ⬝ᵥ z) - (a j₁ ⬝ᵥ v)) with ht
    have ht0 : 0 ≤ t := div_nonneg (hz j₁) (hden j₁ hj₁B).le
    have ht1 : t < 1 := by
      rw [ht, div_lt_one (hden j₁ hj₁B)]
      linarith [(hmemB j₁).mp hj₁B]
    -- the point the walk stops at, read through an arbitrary direction
    set z₀ : Vec ℝ N := (1 - t) • z + t • v with hz₀
    have hdot : ∀ y : Vec ℝ N, y ⬝ᵥ z₀ = (1 - t) * (y ⬝ᵥ z) + t * (y ⬝ᵥ v) := by
      intro y
      rw [hz₀, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have hz₀nonneg : ∀ j, 0 ≤ a j ⬝ᵥ z₀ := by
      intro j
      rw [hdot (a j)]
      by_cases hj : a j ⬝ᵥ v < 0
      · -- this constraint is not passed: `t` is the smallest of the biting times
        have hjB : j ∈ B := (hmemB j).mpr hj
        have hmul : t * ((a j ⬝ᵥ z) - (a j ⬝ᵥ v)) ≤ a j ⬝ᵥ z :=
          calc t * ((a j ⬝ᵥ z) - (a j ⬝ᵥ v))
              ≤ ((a j ⬝ᵥ z) / ((a j ⬝ᵥ z) - (a j ⬝ᵥ v))) * ((a j ⬝ᵥ z) - (a j ⬝ᵥ v)) :=
                mul_le_mul_of_nonneg_right (hj₁min j hjB) (hden j hjB).le
            _ = a j ⬝ᵥ z := div_mul_cancel₀ _ (hden j hjB).ne'
        nlinarith [hmul]
      · push Not at hj
        have h1 : 0 ≤ (1 - t) * (a j ⬝ᵥ z) := mul_nonneg (by linarith) (hz j)
        have h2 : 0 ≤ t * (a j ⬝ᵥ v) := mul_nonneg ht0 hj
        linarith
    -- at the first biting time the constraint that bites is exactly tight
    have hz₀j₁ : a j₁ ⬝ᵥ z₀ = 0 := by
      have hd := hden j₁ hj₁B
      have hc : t * ((a j₁ ⬝ᵥ z) - (a j₁ ⬝ᵥ v)) = a j₁ ⬝ᵥ z := by
        rw [ht]; exact div_mul_cancel₀ _ hd.ne'
      rw [hdot (a j₁)]
      linear_combination -hc
    have hz₀w : 0 < w ⬝ᵥ z₀ := by
      rw [hdot w, hvw, mul_zero, add_zero]
      exact mul_pos (by linarith) hw
    have hz₀S : ∀ i, a (S i) ⬝ᵥ z₀ = 0 := by
      intro i; rw [hdot (a (S i)), hSz i, hvS i]; ring
    -- `a j₁` is new: everything already active annihilates `v`, and it does not
    have hnot : a j₁ ∉ Submodule.span ℝ (Set.range fun i => a (S i)) := by
      intro hmem
      have hle : Submodule.span ℝ (Set.range fun i => a (S i)) ≤ LinearMap.ker (aux_dotL v) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        simpa [aux_dotL] using hvS i
      have : a j₁ ⬝ᵥ v = 0 := by simpa [aux_dotL] using LinearMap.mem_ker.mp (hle hmem)
      linarith [(hmemB j₁).mp hj₁B]
    have hcons : (fun i => a ((Fin.cons j₁ S : Fin (k + 1) → ι) i))
        = Fin.cons (a j₁) fun i => a (S i) := by
      funext i
      refine Fin.cases ?_ (fun i' => ?_) i <;> simp
    refine ih (k + 1) (Fin.cons j₁ S : Fin (k + 1) → ι) z₀ (by omega)
      (by rw [hcons]; exact hind.finCons hnot) (fun i => ?_) hz₀nonneg hz₀w
    refine Fin.cases ?_ (fun i' => ?_) i
    · simpa using hz₀j₁
    · simpa using hz₀S i'


-- =======================================  MAIN THEOREM  ======================================= --

/-- A linear form positive somewhere on a pointed cone is positive on an edge:
a direction `n` linearly independent constraints annihilate. -/
theorem exists_edge_of_cone {n : ℕ} (a : ι → Vec ℝ (n + 1)) (w : Vec ℝ (n + 1))
    (hpt : ∀ y : Vec ℝ (n + 1), (∀ j, a j ⬝ᵥ y = 0) → y = 0)
    (z : Vec ℝ (n + 1)) (hz : ∀ j, 0 ≤ a j ⬝ᵥ z) (hw : 0 < w ⬝ᵥ z) :
    ∃ (S : Fin n → ι) (y : Vec ℝ (n + 1)), LinearIndependent ℝ (fun i => a (S i)) ∧
      (∀ i, a (S i) ⬝ᵥ y = 0) ∧ (∀ j, 0 ≤ a j ⬝ᵥ y) ∧ 0 < w ⬝ᵥ y := by -- --- PROOF ---
  obtain ⟨k, S, y, hk, hind, hSy, hy, hwy⟩ :=
    aux_coneWalk a w hpt (n + 1) 0 Fin.elim0 z (by omega)
      (linearIndependent_empty_type) (fun i => i.elim0) hz hw
  -- `n` of the `k ≥ n` active constraints are already independent
  refine ⟨fun i => S (Fin.castLE (by omega) i), y, ?_, fun i => hSy _, hy, hwy⟩
  exact hind.comp _ (Fin.castLE_injective _)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
