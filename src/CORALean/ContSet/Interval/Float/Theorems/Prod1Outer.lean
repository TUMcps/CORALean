import CORALean.ContSet.Interval.Float.Operations.Prod1
import CORALean.ContSet.Interval.Float.Theorems.TimesOuter
import CORALean.ContSet.Interval.Float.Theorems.MemPoint
import CORALean.ContSet.Interval.Real.Operations.Prod1
import Mathlib.Algebra.BigOperators.Fin

/-!
# `Interval.prod₁` holds every column product

Each member of the exact layer's box has its column products in the stored box, by induction on
the rows with `times_outer` at each step. Not exact: every `times` rounds outward.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.prod₁_outer : ∀ {m : ℕ} (I : Interval (Mat 𝕋 m n)),
    (fun A : Mat ℝ m n => fun j => ∏ i, A i j) '' I.nominal.construct ⊆
      I.prod₁.construct := by -- --- PROOF ---
  -- no rows: the point `1`, whose reading is the real `1`
  intro m
  induction m with
  | zero =>
    intro I
    rintro _ ⟨A, _, rfl⟩ j
    simp only [Interval.prod₁, Fin.foldr_zero, Interval.point, Finset.univ_eq_empty,
      Finset.prod_empty]
    exact ⟨le_of_eq (toReal_one (𝕋 := 𝕋)), le_of_eq (toReal_one (𝕋 := 𝕋)).symm⟩
  | succ m ih =>
    -- the first row times the product of the others, each step `times_outer`
    intro I
    rintro _ ⟨A, hA, rfl⟩
    let row0 : Interval (Vec 𝕋 n) := ⟨fun j => I.inf 0 j, fun j => I.sup 0 j⟩
    have hT : (fun j => ∏ i : Fin m, A i.succ j) ∈
        (Interval.prod₁ (⟨fun i => I.inf i.succ, fun i => I.sup i.succ⟩ :
          Interval (Mat 𝕋 m n))).construct :=
      ih _ ⟨fun i => A i.succ, fun p => hA (p.1.succ, p.2), rfl⟩
    have hrow : A 0 ∈ row0.construct := fun j => hA (0, j)
    have h := Interval.times_outer row0 (Interval.prod₁
      (⟨fun i => I.inf i.succ, fun i => I.sup i.succ⟩ : Interval (Mat 𝕋 m n)))
      ⟨A 0, hrow, _, hT, rfl⟩
    have e : I.prod₁ = row0.times (Interval.prod₁
      (⟨fun i => I.inf i.succ, fun i => I.sup i.succ⟩ : Interval (Mat 𝕋 m n))) := by
      simp only [Interval.prod₁, Fin.foldr_succ]
      rfl
    rw [e]
    convert h using 1
    funext j
    simp [Fin.prod_univ_succ]


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
