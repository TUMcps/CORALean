module

public import CORALean.HybridDynamics.Parallel.Operations.ZonotopeStackProd
public import CORALean.HybridDynamics.Parallel.Theorems.StackApply

@[expose] public section

/-!
# A block of a stacked zonotope's point

The block `i` of the point of `Zonotope.stackProd zs` at coefficients `β` is component `i`'s own
point at the coefficients `β` takes on `i`'s block of generators. This is the whole content of
`ZonotopeStackProdExact`: the blocks are independent.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {k : ℕ} {n : Fin k → ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.stackProd_value (zs : ∀ i, Zonotope (Vec ℝ (n i)))
    (β : Fin (∑ i, (zs i).h) → ℝ) (i : Fin k) :
    unstack ((Zonotope.stackProd zs).c +
        ∑ p : Fin (∑ i, (zs i).h), β p • (Zonotope.stackProd zs).G p) i =
      (zs i).c + ∑ j, β (finSigmaFinEquiv (n := fun i => (zs i).h) ⟨i, j⟩) •
        (zs i).G j := by -- --- PROOF ---
  -- compare coordinate `t` of block `i`, the sum over the stack's coefficients as one over pairs
  classical
  funext t
  simp only [unstack, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [show (Zonotope.stackProd zs).c (finSigmaFinEquiv ⟨i, t⟩) = (zs i).c t from
    stack_apply (fun i => (zs i).c) i t]
  congr 1
  change ∑ p : Fin (∑ i, (zs i).h),
    β p * (Zonotope.stackProd zs).G p (finSigmaFinEquiv ⟨i, t⟩) = _
  -- the generator at pair `⟨c, j⟩`, read at block `i`, is the component's own or zero
  have hG : ∀ (c : Fin k) (j : Fin (zs c).h),
      (Zonotope.stackProd zs).G (finSigmaFinEquiv ⟨c, j⟩) (finSigmaFinEquiv ⟨i, t⟩) =
        Function.update (fun i => (0 : Vec ℝ (n i))) c ((zs c).G j) i t := by
    intro c j
    have e : (finSigmaFinEquiv (n := fun i => (zs i).h)).symm (finSigmaFinEquiv ⟨c, j⟩) =
        ⟨c, j⟩ := Equiv.symm_apply_apply _ _
    have key : ∀ q : (Σ i, Fin (zs i).h), q = ⟨c, j⟩ →
        Function.update (fun i => (0 : Vec ℝ (n i))) q.1 ((zs q.1).G q.2) i t =
          Function.update (fun i => (0 : Vec ℝ (n i))) c ((zs c).G j) i t := by
      rintro q rfl; rfl
    simp only [Zonotope.stackProd, stack_apply]
    exact key _ e
  -- only the pairs of block `i` contribute to the sum
  rw [← (finSigmaFinEquiv (n := fun i => (zs i).h)).sum_comp, Fintype.sum_sigma]
  simp only [hG]
  rw [Finset.sum_eq_single i]
  · simp
  · intro c _ hc
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Function.update_of_ne (Ne.symm hc)]
    simp
  · simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
