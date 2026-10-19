module

public import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullCons
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MulVecConvHullBlock
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MulVecConvHullLast
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemConstructIffOfEq

@[expose] public section

/-!
# What the convex hull's constraint says

Every copy's equations, each at its own block of factors, and the weights summing to `1 - a`
(the weights are `λⱼ - 1` there, [1, Prop. 9]'s shift). A copy's row reads its own factors alone
(`mulVec_convHull_block`) and the last row adds the weights (`mulVec_convHull_last`).

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       13-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The hull's equations hold exactly when every copy's do and the weights add up to what a
convex combination needs. -/
theorem ConPolyZono.mem_convHullCons_iff (a : ℕ) {P : PolyLevelSet p} (h : ∀ i, P.op i = .eq)
    (v : Fin (a * p + a) → ℝ) : -- --- STMT ---
    v ∈ (ConPolyZono.convHullCons a P).construct
      ↔ (∀ j, (fun k => v (Fin.castAdd a (finProdFinEquiv (j, k)))) ∈ P.construct)
        ∧ ∑ j, v (Fin.natAdd (a * p) j) = 1 - (a : ℝ) := by -- --- PROOF ---
  have key : v ∈ (ConPolyZono.convHullCons a P).construct ↔ ∀ i,
      (ConPolyZono.convHullA a P.A *ᵥ PolyZonotope.monomial (ConPolyZono.convHullR a P.R) v) i
        = ConPolyZono.convHullB a P.b i :=
    PolyLevelSet.mem_construct_iff_of_eq fun _ => rfl
  rw [key]
  simp only [PolyLevelSet.mem_construct_iff_of_eq h]
  constructor
  · intro hsat
    refine ⟨fun j i => ?_, ?_⟩
    · have h := hsat (Fin.castAdd 1 (finProdFinEquiv (j, i)))
      rw [ConPolyZono.mulVec_convHull_block] at h
      simpa only [ConPolyZono.convHullB, ConPolyZono.repVec, Fin.append_left,
        Equiv.symm_apply_apply] using h
    · -- the weight row
      have h := hsat (Fin.natAdd (a * P.m) (0 : Fin 1))
      rw [ConPolyZono.mulVec_convHull_last] at h
      simpa only [ConPolyZono.convHullB, Fin.append_right] using h
  · rintro ⟨hj, hl⟩
    have key : ∀ (j : Fin a) (i : Fin P.m),
        (ConPolyZono.convHullA a P.A *ᵥ PolyZonotope.monomial (ConPolyZono.convHullR a P.R) v)
            (Fin.castAdd 1 (finProdFinEquiv (j, i)))
          = ConPolyZono.convHullB a P.b (Fin.castAdd 1 (finProdFinEquiv (j, i))) := by
      intro j i
      rw [ConPolyZono.mulVec_convHull_block]
      simpa only [ConPolyZono.convHullB, ConPolyZono.repVec, Fin.append_left,
        Equiv.symm_apply_apply] using hj j i
    -- every row is a copy's or the weight row, and `finProdFinEquiv` says which
    refine Fin.addCases (fun r => ?_) (fun r => ?_)
    · have h := key (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2
      rwa [Prod.mk.eta, Equiv.apply_symm_apply] at h
    · have h : r = 0 := Subsingleton.elim r 0
      subst h
      rw [ConPolyZono.mulVec_convHull_last, hl]
      simp only [ConPolyZono.convHullB, Fin.append_right]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
