import CORALean.NN.Theorems.Verified
import CORALean.Global.LinProg.LinProg

/-!
# Robust classification, as a specification the outputs avoid

The requirement a classifier is normally verified against: over a whole input
set — an image and everything within a perturbation of it — the same label wins.
Written as an unsafe set, since what must not happen is that some other label
catches up, and then it is checked by the same theorem everything else is.

`m - 1` bounds discharge it, one per rival label, each in the direction
`eⱼ - e_l` — the objective "how much closer can `j` get to `l`". Negative means
it never catches up. Those are the objects `Global.LinProg` already produces,
so a classifier is verified with no machinery beyond a bound per rival.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}

/-- Some label other than `l` at least ties it, so `l` is not the unique
winner. -/
def misclassified (m : ℕ) (l : Fin m) : Set (Vec ℝ m) := {y | ∃ j, j ≠ l ∧ y l ≤ y j}

/-- How far label `j` closes the gap on label `l`: the direction each of the
`m - 1` bounds runs in. -/
def marginDir (m : ℕ) (j l : Fin m) : Vec ℝ m →ₗ[ℝ] ℝ :=
  (LinearMap.proj j : Vec ℝ m →ₗ[ℝ] ℝ) - (LinearMap.proj l : Vec ℝ m →ₗ[ℝ] ℝ)

theorem marginDir_apply (j l : Fin m) (y : Vec ℝ m) : marginDir m j l y = y j - y l := by
  rw [marginDir, LinearMap.sub_apply]
  rfl

theorem disjoint_misclassified_of_bounds {O : Set (Vec ℝ m)} (l : Fin m)
    (u : ∀ j, SupportBound O (marginDir m j l))
    (h : ∀ j, j ≠ l → (u j).val < 0) : Disjoint O (misclassified m l) := by
  rw [Set.disjoint_left]
  rintro y hy ⟨j, hj, hle⟩
  have hb := (u j).le y hy
  rw [marginDir_apply] at hb
  linarith [h j hj]

/-- Every input in the set is classified `l`, on the strength of one bound per
rival label against the propagated output set. -/
theorem NeuralNetwork.classifies (nn : NeuralNetwork S n m) (X : S n) (l : Fin m)
    (u : ∀ j, SupportBound (construct (nn.propagate X))
      (marginDir m j l))
    (h : ∀ j, j ≠ l → (u j).val < 0) {x : Vec ℝ n} (hx : x ∈ construct X)
    {j : Fin m} (hj : j ≠ l) : nn.eval x j < nn.eval x l := by
  have hd := disjoint_misclassified_of_bounds l u h
  have hmem := nn.propagate_outer X x hx
  have hnot := Set.disjoint_left.mp hd hmem
  by_contra hc
  exact hnot ⟨j, hj, not_lt.mp hc⟩

theorem NeuralNetwork.holds_robustness (nn : NeuralNetwork S n m) (X : S n) (l : Fin m)
    (u : ∀ j, SupportBound (construct (nn.propagate X))
      (marginDir m j l))
    (h : ∀ j, j ≠ l → (u j).val < 0) :
    (Specification.unsafeSet (misclassified m l)).Holds (nn.outputSet X) :=
  nn.holds_of_propagate X _ (disjoint_misclassified_of_bounds l u h)

end CORALean.Real
