module

public import CORALean.ContSet.Interval.Real.Theorems.MulBetweenCorners
public import CORALean.ContSet.Taylm.Real.Definitions.Box
public import CORALean.ContSet.Taylm.Real.Operations.PolyBoxBounds
public import CORALean.ContSet.Taylm.Real.Taylm
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import CORALean.ContSet.Taylm.Real.Theorems.PowBoundsMem
public import CORALean.ContSet.Taylm.Real.Theorems.ProdBoundsMem

@[expose] public section

/-!
# Interval evaluation encloses a polynomial over a box

[1, Eq. 12]: `B(P) ⊆ Σ c [x]ⁱ [y]ʲ`. A point of the box makes every coordinate power lie in
its interval power, the product in the interval product, and the term and the sum follow.

## Inputs
* `L` – terms of the polynomial
* `B` – box
* `t` – point

## Hypotheses
* `ht` – point lies in the box

## Conclusion
* the polynomial's value lies in its bounds on the box

## References

* [1] M. Althoff, D. Grebenyuk, and N. Kochdumper. "Implementation of Taylor Models in CORA
      2018". In Proc. of the 5th International Workshop on Applied Verification of Continuous
      and Hybrid Systems (ARCH18), EPiC Series in Computing, vol. 54, pp. 145-173, 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.polyBoxBounds_mem (L : List (ℝ × (Fin n → ℕ))) {B : Fin n → Interval ℝ} {t : Vec ℝ n}
    (ht : Taylm.InBox B t) :
    (Taylm.polyBoxBounds L B).inf ≤ Taylm.polyOf L t ∧
      Taylm.polyOf L t ≤ (Taylm.polyBoxBounds L B).sup := by -- --- PROOF ---
  -- one term
  have hterm : ∀ a : ℝ × (Fin n → ℕ), (Taylm.termBoxBounds B a).inf ≤ a.1 * Taylm.monomial a.2 t ∧
      a.1 * Taylm.monomial a.2 t ≤ (Taylm.termBoxBounds B a).sup := by
    intro a
    have hM := Taylm.prodBounds_mem (List.ofFn fun k => Taylm.powBounds (B k).inf (B k).sup (a.2 k))
      (List.ofFn fun k => t k ^ a.2 k) (by simp) fun i h₁ h₂ => by
        simp only [List.getElem_ofFn]
        exact Taylm.powBounds_mem (ht ⟨i, by simpa using h₁⟩).1 (ht ⟨i, by simpa using h₁⟩).2 _
    rw [List.prod_ofFn] at hM
    exact Interval.mul_between_corners (le_refl a.1) (le_refl a.1) hM.1 hM.2
  induction L with
  | nil => simp [Taylm.polyBoxBounds]
  | cons a L ih =>
    simp only [Taylm.polyBoxBounds, List.map_cons, List.sum_cons, Taylm.polyOf_cons] at ih ⊢
    exact ⟨add_le_add (hterm a).1 ih.1, add_le_add (hterm a).2 ih.2⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
