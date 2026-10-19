module

public import CORALean.ContSet.StarSet.Real.Operations.RowBounds
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# The bounds of a neuron hold

Every point of the star set has the neuron's value between the two bounds: the row is its center
plus `Σ G_jk (α_k - mid_k)`, and each factor is within its radius of the middle of its box.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem StarSet.rowBounds_mem {P : ℕ → Type} [∀ m, ContSet (P m) (Vec ℝ m)] {n : ℕ}
    (s : StarSet P n) (j : Fin n) {x : Vec ℝ n}
    (hx : x ∈ s.construct) :
    (s.rowBounds j).inf ≤ x j ∧ x j ≤ (s.rowBounds j).sup := by -- --- PROOF ---
  obtain ⟨α, ⟨hα, -⟩, hxα⟩ := hx
  -- each factor is within its radius of the middle of its box
  have hterm : ∀ k, |s.G j k * (α k - (s.dom.inf k + s.dom.sup k) / 2)|
      ≤ |s.G j k * ((s.dom.sup k - s.dom.inf k) / 2)| := fun k => by
    rw [abs_mul, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have h1 : s.dom.inf k ≤ α k ∧ α k ≤ s.dom.sup k := hα k
    have h2 : 0 ≤ (s.dom.sup k - s.dom.inf k) / 2 := by linarith [h1.1, h1.2]
    rw [abs_of_nonneg h2, abs_le]
    constructor <;> linarith [h1.1, h1.2]
  -- so the deviation of the row from its center is within the radius
  have hsum : |∑ k, s.G j k * (α k - (s.dom.inf k + s.dom.sup k) / 2)|
      ≤ ∑ k, |s.G j k * ((s.dom.sup k - s.dom.inf k) / 2)| :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => hterm k)
  -- the row is its center plus that deviation
  have hxj : x j = (s.c j + ∑ k, s.G j k * ((s.dom.inf k + s.dom.sup k) / 2))
      + ∑ k, s.G j k * (α k - (s.dom.inf k + s.dom.sup k) / 2) := by
    rw [hxα j]
    have : ∑ k, s.G j k * α k = ∑ k, s.G j k * ((s.dom.inf k + s.dom.sup k) / 2)
        + ∑ k, s.G j k * (α k - (s.dom.inf k + s.dom.sup k) / 2) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [add_assoc, ← this]
  have h := abs_le.mp hsum
  simp only [StarSet.rowBounds]
  constructor <;> linarith [h.1, h.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
