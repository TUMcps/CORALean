import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullA
import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullB
import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullEC
import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecBlkDiag
import CORALean.ContSet.ConPolyZono.Real.Operations.ProdBlkDiag
import Mathlib.Algebra.BigOperators.Fin

/-!
# The constraint system of the convex hull, split

[1, Prop. 9]'s constraints say two separate things, and this is the split: each
of the `a` copies satisfies the linear combination's own system, over its own
block of factors, and the `a` fresh weight factors sum to `1 - a`.

The second is the last row, whose `1` entries meet the weight columns alone.
Since a weight factor `λ` stands for the weight `1 + λ`, that row is exactly
`∑ (1 + λⱼ) = 1`, and the factor cube's `|λⱼ| ≤ 1` is what makes each weight
non-negative — together, a point of the simplex.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       13-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A copy's constraint column names that copy's own monomial. -/
theorem ConPolyZono.aux_monomial_con {a p s : ℕ} (EC : Fin p → Fin s → ℕ)
    (v : Fin (a * p + a) → ℝ) (j : Fin a) (l : Fin s) :
    PolyZonotope.monomial (ConPolyZono.convHullEC a EC) v (Fin.castAdd a (finProdFinEquiv (j, l)))
      = PolyZonotope.monomial EC
        (fun k => v (Fin.castAdd a (finProdFinEquiv (j, k)))) l := by -- --- PROOF ---
  have h₁ : (∏ x : Fin (a * p), v (Fin.castAdd a x) ^ ConPolyZono.convHullEC a EC
      (Fin.castAdd a x) (Fin.castAdd a (finProdFinEquiv (j, l))))
      = ∏ k, v (Fin.castAdd a (finProdFinEquiv (j, k))) ^ EC k l := by
    simp only [ConPolyZono.convHullEC, Fin.append_left]
    exact ConPolyZono.prod_blkDiag EC (fun x => v (Fin.castAdd a x)) j l
  -- the weight rows are zero throughout the copies' columns
  have h₂ : (∏ j' : Fin a, v (Fin.natAdd (a * p) j') ^ ConPolyZono.convHullEC a EC
      (Fin.natAdd (a * p) j') (Fin.castAdd a (finProdFinEquiv (j, l)))) = 1 := by
    simp [ConPolyZono.convHullEC]
  rw [PolyZonotope.monomial, Fin.prod_univ_add, h₁, h₂, mul_one, PolyZonotope.monomial]

/-- A weight column names its own weight factor. -/
theorem ConPolyZono.aux_monomial_lam {a p s : ℕ} (EC : Fin p → Fin s → ℕ)
    (v : Fin (a * p + a) → ℝ) (j : Fin a) :
    PolyZonotope.monomial (ConPolyZono.convHullEC a EC) v (Fin.natAdd (a * s) j)
      = v (Fin.natAdd (a * p) j) := by -- --- PROOF ---
  have h₁ : (∏ x : Fin (a * p), v (Fin.castAdd a x) ^ ConPolyZono.convHullEC a EC
      (Fin.castAdd a x) (Fin.natAdd (a * s) j)) = 1 := by
    simp [ConPolyZono.convHullEC]
  -- and only `j`'s own weight row carries a power here
  have h₂ : (∏ j' : Fin a, v (Fin.natAdd (a * p) j') ^ ConPolyZono.convHullEC a EC
      (Fin.natAdd (a * p) j') (Fin.natAdd (a * s) j)) = v (Fin.natAdd (a * p) j) := by
    simp only [ConPolyZono.convHullEC, Fin.append_right]
    refine (Finset.prod_eq_single j (fun j' _ hj' => ?_)
      (fun hj => absurd (Finset.mem_univ j) hj)).trans ?_
    · simp [ConPolyZono.unitCol, Ne.symm hj']
    · simp [ConPolyZono.unitCol]
  rw [PolyZonotope.monomial, Fin.prod_univ_add, h₁, h₂, one_mul]

/-- A copy's constraint row is the linear combination's, over that copy. -/
theorem ConPolyZono.aux_mulVec_block {a p m s : ℕ} (A : Mat ℝ m s) (EC : Fin p → Fin s → ℕ)
    (v : Fin (a * p + a) → ℝ) (j : Fin a) (i : Fin m) :
    (ConPolyZono.convHullA a A *ᵥ PolyZonotope.monomial (ConPolyZono.convHullEC a EC) v)
        (Fin.castAdd 1 (finProdFinEquiv (j, i)))
      = (A *ᵥ PolyZonotope.monomial EC
          (fun k => v (Fin.castAdd a (finProdFinEquiv (j, k))))) i := by -- --- PROOF ---
  show (∑ y, ConPolyZono.convHullA a A (Fin.castAdd 1 (finProdFinEquiv (j, i))) y
      * PolyZonotope.monomial (ConPolyZono.convHullEC a EC) v y)
    = ∑ l, A i l * PolyZonotope.monomial EC _ l
  rw [Fin.sum_univ_add]
  -- the weight columns are zero on every copy's row
  simp only [ConPolyZono.convHullA, Fin.append_left, Fin.append_right, zero_mul,
    Finset.sum_const_zero, add_zero]
  rw [ConPolyZono.mulVec_blkDiag A
    (fun y => PolyZonotope.monomial (ConPolyZono.convHullEC a EC) v (Fin.castAdd a y)) j i]
  exact Finset.sum_congr rfl fun l _ => by rw [ConPolyZono.aux_monomial_con]

/-- The last row adds the weight factors and nothing else. -/
theorem ConPolyZono.aux_mulVec_last {a p m s : ℕ} (A : Mat ℝ m s) (EC : Fin p → Fin s → ℕ)
    (v : Fin (a * p + a) → ℝ) :
    (ConPolyZono.convHullA a A *ᵥ PolyZonotope.monomial (ConPolyZono.convHullEC a EC) v)
        (Fin.natAdd (a * m) (0 : Fin 1))
      = ∑ j, v (Fin.natAdd (a * p) j) := by -- --- PROOF ---
  show (∑ y, ConPolyZono.convHullA a A (Fin.natAdd (a * m) (0 : Fin 1)) y
      * PolyZonotope.monomial (ConPolyZono.convHullEC a EC) v y) = _
  rw [Fin.sum_univ_add]
  -- the copies' columns are zero on this row
  simp only [ConPolyZono.convHullA, Fin.append_left, Fin.append_right, zero_mul,
    Finset.sum_const_zero, zero_add, one_mul]
  exact Finset.sum_congr rfl fun j _ => ConPolyZono.aux_monomial_lam EC v j


-- =======================================  MAIN THEOREM  ======================================= --

/-- The hull's system holds exactly when every copy's does and the weights add
up to what a convex combination needs. -/
theorem ConPolyZono.holds_convHull_iff {a p m s : ℕ} (A : Mat ℝ m s) (b : Interval (Vec ℝ m))
    (EC : Fin p → Fin s → ℕ) (v : Fin (a * p + a) → ℝ) :
    ConPolyZono.holds (ConPolyZono.convHullA a A) (ConPolyZono.convHullB a b)
        (ConPolyZono.convHullEC a EC) v
      ↔ (∀ j, ConPolyZono.holds A b EC (fun k => v (Fin.castAdd a (finProdFinEquiv (j, k)))))
        ∧ ∑ j, v (Fin.natAdd (a * p) j) = 1 - (a : ℝ) := by -- --- PROOF ---
  constructor
  · intro hsat
    refine ⟨fun j i => ?_, ?_⟩
    · have h := hsat (Fin.castAdd 1 (finProdFinEquiv (j, i)))
      rw [ConPolyZono.aux_mulVec_block] at h
      simpa only [ConPolyZono.convHullB, ConPolyZono.repVec, Fin.append_left,
        Equiv.symm_apply_apply] using h
    · -- the weight row is a point interval, so its two bounds are one equation
      have h := hsat (Fin.natAdd (a * m) (0 : Fin 1))
      rw [ConPolyZono.aux_mulVec_last] at h
      simp only [ConPolyZono.convHullB, Fin.append_right] at h
      linarith [h.1, h.2]
  · rintro ⟨hj, hl⟩
    have key : ∀ (j : Fin a) (i : Fin m),
        (ConPolyZono.convHullB a b).inf (Fin.castAdd 1 (finProdFinEquiv (j, i)))
            ≤ (ConPolyZono.convHullA a A
              *ᵥ PolyZonotope.monomial (ConPolyZono.convHullEC a EC) v)
              (Fin.castAdd 1 (finProdFinEquiv (j, i)))
          ∧ (ConPolyZono.convHullA a A
              *ᵥ PolyZonotope.monomial (ConPolyZono.convHullEC a EC) v)
              (Fin.castAdd 1 (finProdFinEquiv (j, i)))
            ≤ (ConPolyZono.convHullB a b).sup (Fin.castAdd 1 (finProdFinEquiv (j, i))) := by
      intro j i
      rw [ConPolyZono.aux_mulVec_block]
      simpa only [ConPolyZono.convHullB, ConPolyZono.repVec, Fin.append_left,
        Equiv.symm_apply_apply] using hj j i
    -- every row is a copy's or the weight row, and `finProdFinEquiv` says which
    refine Fin.addCases (fun r => ?_) (fun r => ?_)
    · have h := key (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2
      rwa [Prod.mk.eta, Equiv.apply_symm_apply] at h
    · have h : r = 0 := Subsingleton.elim r 0
      subst h
      rw [ConPolyZono.aux_mulVec_last, hl]
      simp only [ConPolyZono.convHullB, Fin.append_right]
      exact ⟨le_refl _, le_refl _⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
