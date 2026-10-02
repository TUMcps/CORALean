import CORALean.ContSet.Interval.Float.Theorems.MatMulOuter
import CORALean.ContSet.Interval.Float.Theorems.MemMatIff
import CORALean.ContSet.Interval.Real.Operations.MatMul

/-!
# A real box product inside a float one, the factors' boxes inside

If the real boxes `X`, `Y` are non-empty and inside the float boxes `X'`, `Y'`,
the real product box `matMul X Y` is inside the float `matMul X' Y'` — a box, not
only the products of its members, which is what a point that is merely between
the real product's endpoints needs.

Entry by entry the real endpoint is attained: the least corner sum is `(M N)ᵢⱼ`
for the member `M` whose row `i` takes, entry by entry, the endpoint the least
corner product picks, and `N` likewise in column `j`, the other entries any
member's. The float product holds `M N` (`matMul_outer`), so its endpoint is no
further in than the real one.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n p : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The least corner product is attained at a pair of endpoints. -/
theorem aux_mulLo_attained {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    ∃ y x, (a ≤ y ∧ y ≤ b) ∧ (c ≤ x ∧ x ≤ d) ∧
      y * x = Real.Interval.mulLo a b c d := by -- --- PROOF ---
  unfold Real.Interval.mulLo
  rcases min_choice (min (a * c) (a * d)) (min (b * c) (b * d)) with h | h <;> rw [h]
  · rcases min_choice (a * c) (a * d) with h' | h' <;> rw [h']
    · exact ⟨a, c, ⟨le_rfl, hab⟩, ⟨le_rfl, hcd⟩, rfl⟩
    · exact ⟨a, d, ⟨le_rfl, hab⟩, ⟨hcd, le_rfl⟩, rfl⟩
  · rcases min_choice (b * c) (b * d) with h' | h' <;> rw [h']
    · exact ⟨b, c, ⟨hab, le_rfl⟩, ⟨le_rfl, hcd⟩, rfl⟩
    · exact ⟨b, d, ⟨hab, le_rfl⟩, ⟨hcd, le_rfl⟩, rfl⟩

/-- The greatest likewise. -/
theorem aux_mulHi_attained {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    ∃ y x, (a ≤ y ∧ y ≤ b) ∧ (c ≤ x ∧ x ≤ d) ∧
      y * x = Real.Interval.mulHi a b c d := by -- --- PROOF ---
  unfold Real.Interval.mulHi
  rcases max_choice (max (a * c) (a * d)) (max (b * c) (b * d)) with h | h <;> rw [h]
  · rcases max_choice (a * c) (a * d) with h' | h' <;> rw [h']
    · exact ⟨a, c, ⟨le_rfl, hab⟩, ⟨le_rfl, hcd⟩, rfl⟩
    · exact ⟨a, d, ⟨le_rfl, hab⟩, ⟨hcd, le_rfl⟩, rfl⟩
  · rcases max_choice (b * c) (b * d) with h' | h' <;> rw [h']
    · exact ⟨b, c, ⟨hab, le_rfl⟩, ⟨le_rfl, hcd⟩, rfl⟩
    · exact ⟨b, d, ⟨hab, le_rfl⟩, ⟨hcd, le_rfl⟩, rfl⟩

/-- A real product entry attained at chosen row and column entries is bounded by
the float product's endpoints. -/
theorem aux_entry_bound {X : Real.Interval (Mat ℝ m n)} {Y : Real.Interval (Mat ℝ n p)}
    {X' : Interval (Mat 𝕋 m n)} {Y' : Interval (Mat 𝕋 n p)} {M₀ : Mat ℝ m n} {N₀ : Mat ℝ n p}
    (hM₀ : M₀ ∈ X.construct) (hN₀ : N₀ ∈ Y.construct) (hX : X.construct ⊆ X'.construct)
    (hY : Y.construct ⊆ Y'.construct) (i : Fin m) (j : Fin p) {y x : Fin n → ℝ}
    (hy : ∀ l, X.inf i l ≤ y l ∧ y l ≤ X.sup i l) (hx : ∀ l, Y.inf l j ≤ x l ∧ x l ≤ Y.sup l j) :
    toReal ((Interval.matMul X' Y').inf i j) ≤ ∑ l, y l * x l ∧
      ∑ l, y l * x l ≤ toReal ((Interval.matMul X' Y').sup i j) := by -- --- PROOF ---
  classical
  -- row `i` of one member and column `j` of another, overwritten
  set M : Mat ℝ m n := Matrix.of fun i' l => if i' = i then y l else M₀ i' l
  set N : Mat ℝ n p := Matrix.of fun l j' => if j' = j then x l else N₀ l j'
  have hM : M ∈ X.construct := Real.Interval.mem_mat_iff.mpr fun i' l => by
    by_cases h : i' = i
    · subst h; simpa [M] using hy l
    · simpa [M, h] using Real.Interval.mem_mat_iff.mp hM₀ i' l
  have hN : N ∈ Y.construct := Real.Interval.mem_mat_iff.mpr fun l j' => by
    by_cases h : j' = j
    · subst h; simpa [N] using hx l
    · simpa [N, h] using Real.Interval.mem_mat_iff.mp hN₀ l j'
  have h := Interval.mem_mat_iff.mp (Interval.matMul_outer X' Y' (hX hM) (hY hN)) i j
  have hMN : (M * N) i j = ∑ l, y l * x l := by simp [M, N, Matrix.mul_apply]
  rwa [hMN] at h


-- =======================================  MAIN THEOREM  ======================================= --

/-- Non-empty real boxes inside float ones have their real product box inside the
float product. -/
theorem Interval.matMul_subset {X : Real.Interval (Mat ℝ m n)} {Y : Real.Interval (Mat ℝ n p)}
    {X' : Interval (Mat 𝕋 m n)} {Y' : Interval (Mat 𝕋 n p)} {M₀ : Mat ℝ m n} {N₀ : Mat ℝ n p}
    (hM₀ : M₀ ∈ X.construct) (hN₀ : N₀ ∈ Y.construct) (hX : X.construct ⊆ X'.construct)
    (hY : Y.construct ⊆ Y'.construct) :
    (Real.Interval.matMul X Y).construct ⊆ (Interval.matMul X' Y').construct := by -- --- PROOF ---
  intro P hP
  have hXw : ∀ i l, X.inf i l ≤ X.sup i l := fun i l =>
    (Real.Interval.mem_mat_iff.mp hM₀ i l).1.trans (Real.Interval.mem_mat_iff.mp hM₀ i l).2
  have hYw : ∀ l j, Y.inf l j ≤ Y.sup l j := fun l j =>
    (Real.Interval.mem_mat_iff.mp hN₀ l j).1.trans (Real.Interval.mem_mat_iff.mp hN₀ l j).2
  refine Interval.mem_mat_iff.mpr fun i j => ?_
  have hPij := Real.Interval.mem_mat_iff.mp hP i j
  -- the real endpoints, each attained by a pair of members
  choose yL xL hyL hxL hL using fun l => aux_mulLo_attained (hXw i l) (hYw l j)
  choose yH xH hyH hxH hH using fun l => aux_mulHi_attained (hXw i l) (hYw l j)
  have hlo := (aux_entry_bound hM₀ hN₀ hX hY i j hyL hxL).1
  have hhi := (aux_entry_bound hM₀ hN₀ hX hY i j hyH hxH).2
  simp only [hL, hH] at hlo hhi
  exact ⟨hlo.trans hPij.1, hPij.2.trans hhi⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
