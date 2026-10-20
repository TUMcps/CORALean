module

public import CORALean.ContSet.Interval.Real.Operations.Prod1
public import CORALean.ContSet.Interval.Real.Theorems.TimesExact
public import CORALean.ContSet.Interval.Real.Theorems.IsNonempty
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# `Interval.prod₁` is exactly the set of column products

For a nonempty box, the interval product of the rows is exactly the set of entrywise products of
one row from each: each step `times` is exact (`times_exact`) and the rows are independent. This
holds for the product of independent entries only; a matrix reused twice would not be exact.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the column-product box is exactly the set of column products
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem Interval.aux_prod₁_succ (I : Interval (Mat ℝ (m + 1) n)) :
    I.prod₁ = (⟨fun j => I.inf 0 j, fun j => I.sup 0 j⟩ : Interval (Vec ℝ n)).times
      (Interval.prod₁ (⟨fun i => I.inf i.succ, fun i => I.sup i.succ⟩ :
        Interval (Mat ℝ m n))) := by
  simp only [Interval.prod₁, Fin.foldr_succ]

/-- A box that is exactly the image of a nonempty set is nonempty. -/
theorem Interval.aux_nonempty_of_image {S : Set (Mat ℝ m n)} (hS : S.Nonempty)
    {J : Interval (Vec ℝ n)} {f : Mat ℝ m n → Vec ℝ n} (h : J.construct = f '' S) :
    J.IsNonempty := by
  rw [Interval.isNonempty_iff, h]
  exact hS.image f


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.prod₁_exact : ∀ {m : ℕ} {I : Interval (Mat ℝ m n)}, I.IsNonempty →
    I.prod₁.construct =
      (fun A : Mat ℝ m n => fun j => ∏ i, A i j) '' I.construct := by -- --- PROOF ---
  -- no rows: the empty product is the point `1`
  intro m
  induction m with
  | zero =>
    intro I _
    ext z
    simp only [Interval.prod₁, Fin.foldr_zero, Interval.point, Set.mem_image,
      Finset.univ_eq_empty, Finset.prod_empty]
    constructor
    · intro hz
      refine ⟨fun i => i.elim0, fun p => p.1.elim0, funext fun j => ?_⟩
      exact (le_antisymm (hz j).2 (hz j).1).symm
    · rintro ⟨A, _, rfl⟩ j
      exact ⟨le_refl _, le_refl _⟩
  | succ m ih =>
    -- the first row times the product of the others, each step exact
    intro I hI
    set T : Interval (Mat ℝ m n) := ⟨fun i => I.inf i.succ, fun i => I.sup i.succ⟩ with hT
    have hTne : T.IsNonempty := fun p => hI (p.1.succ, p.2)
    have hrow : (⟨fun j => I.inf 0 j, fun j => I.sup 0 j⟩ : Interval (Vec ℝ n)).IsNonempty :=
      fun j => hI (0, j)
    have hTp : T.prod₁.IsNonempty :=
      Interval.aux_nonempty_of_image ((Interval.isNonempty_iff _).1 hTne) (ih hTne)
    rw [Interval.aux_prod₁_succ, Interval.times_exact hrow hTp, ih hTne]
    ext z
    constructor
    · -- a first row and a tail matrix make one matrix of the box
      rintro ⟨x, hx, _, ⟨A', hA', rfl⟩, rfl⟩
      refine ⟨Fin.cons x A', fun p => ?_, funext fun j => ?_⟩
      · obtain ⟨i, j⟩ := p
        refine Fin.cases ?_ (fun i => ?_) i
        · exact hx j
        · exact hA' (i, j)
      · simp [Fin.prod_univ_succ]
    · rintro ⟨A, hA, rfl⟩
      refine ⟨A 0, fun j => hA (0, j), _, ⟨fun i => A i.succ, fun p => hA (p.1.succ, p.2),
        rfl⟩, funext fun j => ?_⟩
      simp [Fin.prod_univ_succ]


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
