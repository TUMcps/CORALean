import CORALean.ContDynamics.NonlinDASys.Operations.ComposeSubsystems
import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMemIff

/-!
# `composeSubsystems` is the Minkowski sum of the mapped sets

[1, Eq. 15]: the zonotope `NonlinDASys.composeSubsystems` denotes exactly the sum of the sets
`Φ⁽ⁱ⁾ R⁽ⁱ⁾(τ_k)`, with no overapproximation.

## References

* [1] M. Althoff. "Formal and Compositional Analysis of Power Systems using Reachable Sets".
      IEEE Transactions on Power Systems, 29(5):2270-2280, 2014.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix Pointwise

variable {ns n : ℕ} {d : Fin ns → ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The fold over any list of subsystems denotes the list's sum of sets. -/
theorem NonlinDASys.aux_composeSubsystems_foldr (Φ : ∀ i, Mat ℝ n (d i))
    (R : ∀ i, Zonotope (Vec ℝ (d i))) (l : List (Fin ns)) :
    (l.foldr (fun i Z => (Zonotope.mtimes (Φ i) (R i)).plus Z) (Zonotope.ofPoint 0)).construct
      = (l.map fun i => (Φ i *ᵥ ·) '' (R i).construct).sum := by -- --- PROOF ---
  induction l with
  | nil =>
      ext x
      rw [List.foldr_nil, List.map_nil, List.sum_nil, Zonotope.mem_ofPoint_iff]
      exact Iff.rfl
  | cons i l ih =>
      rw [List.foldr_cons, ← Zonotope.plus_exact, ih, List.map_cons, List.sum_cons,
        Zonotope.mtimes_exact]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 15]: `Φ⁽¹⁾R⁽¹⁾ ⊕ ... ⊕ Φ⁽ⁿˢ⁾R⁽ⁿˢ⁾` is the sum of the mapped sets. -/
theorem NonlinDASys.composeSubsystems_exact (Φ : ∀ i, Mat ℝ n (d i))
    (R : ∀ i, Zonotope (Vec ℝ (d i))) :
    (NonlinDASys.composeSubsystems Φ R).construct
      = ∑ i, (Φ i *ᵥ ·) '' (R i).construct := by
  rw [Fin.sum_univ_def]
  exact NonlinDASys.aux_composeSubsystems_foldr Φ R _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
