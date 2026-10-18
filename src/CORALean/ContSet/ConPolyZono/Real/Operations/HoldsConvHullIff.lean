module

public import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullB
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MulVecConvHullBlock
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MulVecConvHullLast

@[expose] public section

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

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       13-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- The hull's system holds exactly when every copy's does and the weights add
up to what a convex combination needs. -/
theorem ConPolyZono.holds_convHull_iff {a p m q : ℕ} (A : Mat ℝ m q) (b : Vec ℝ m)
    (R : Fin p → Fin q → ℕ) (v : Fin (a * p + a) → ℝ) : -- --- STMT ---
    ConPolyZono.holds (ConPolyZono.convHullA a A) (ConPolyZono.convHullB a b)
        (ConPolyZono.convHullR a R) v
      ↔ (∀ j, ConPolyZono.holds A b R (fun k => v (Fin.castAdd a (finProdFinEquiv (j, k)))))
        ∧ ∑ j, v (Fin.natAdd (a * p) j) = 1 - (a : ℝ) := by -- --- PROOF ---
  constructor
  · intro hsat
    refine ⟨fun j i => ?_, ?_⟩
    · have h := hsat (Fin.castAdd 1 (finProdFinEquiv (j, i)))
      rw [ConPolyZono.mulVec_convHull_block] at h
      simpa only [ConPolyZono.convHullB, ConPolyZono.repVec, Fin.append_left,
        Equiv.symm_apply_apply] using h
    · -- the weight row
      have h := hsat (Fin.natAdd (a * m) (0 : Fin 1))
      rw [ConPolyZono.mulVec_convHull_last] at h
      simpa only [ConPolyZono.convHullB, Fin.append_right] using h
  · rintro ⟨hj, hl⟩
    have key : ∀ (j : Fin a) (i : Fin m),
        (ConPolyZono.convHullA a A *ᵥ PolyZonotope.monomial (ConPolyZono.convHullR a R) v)
            (Fin.castAdd 1 (finProdFinEquiv (j, i)))
          = ConPolyZono.convHullB a b (Fin.castAdd 1 (finProdFinEquiv (j, i))) := by
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
