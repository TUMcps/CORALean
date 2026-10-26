module

public import CORALean.ContSet.Interval.Real.Theorems.MemAppendIff
public import CORALean.ContSet.PolyLevelSet.Real.Operations.Relax
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialIdentE
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusELeft
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusERight
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# What `PolyLevelSet.relax` denotes

The points `(x, y)` at which every original row, shifted by `sᵢ yᵢ`, meets its operator
(`aux_eval_relax`).

## Inputs
* `P` – polynomial level set
* `s` – row slack coefficients
* `D` – box of the slack variables
* `x` – point

## Hypotheses
* none

## Conclusion
* `x` lies in the relaxed set iff each shifted row meets its operator
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A relaxed row's value: the original row's, plus the slack its own variable carries. -/
private theorem PolyLevelSet.aux_eval_relax (P : PolyLevelSet n) (s : Vec ℝ P.m)
    (D : Interval (Vec ℝ P.m)) (x : Vec ℝ (n + P.m)) (i : Fin P.m) : -- --- CONCL ---
    (P.relax s D).eval x i
      = P.eval (fun k => x (Fin.castAdd P.m k)) i + s i * x (Fin.natAdd n i) := by -- --- PROOF ---
  have hrow : ((P.relax s D).A *ᵥ PolyZonotope.monomial (P.relax s D).R x) i
      = (P.A *ᵥ PolyZonotope.monomial P.R (fun k => x (Fin.castAdd P.m k))) i
        + s i * x (Fin.natAdd n i) := by
    show ∑ l : Fin (P.q + P.m), Fin.append (P.A i) (Pi.single i (s i)) l
        * PolyZonotope.monomial (PolyZonotope.plusE P.R (PolyZonotope.identE P.m)) x l = _
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, PolyZonotope.monomial_plusE_left,
      PolyZonotope.monomial_plusE_right, PolyZonotope.monomial_identE]
    congr 1
    -- the slack columns: only row `i`'s own variable has a nonzero coefficient
    rw [Finset.sum_eq_single i (fun r _ hr => by rw [Pi.single_eq_of_ne hr, zero_mul])
      (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same]
  show ((P.relax s D).A *ᵥ _) i - P.b i = (P.A *ᵥ _) i - P.b i + _
  rw [hrow]
  ring


-- =======================================  MAIN THEOREM  ======================================= --

/-- A point `(x, y)` of the relaxed set has `x` in `P`'s box, `y` in `D`, and meets every row
`(A μ_R(x) - b)ᵢ + sᵢ yᵢ ⋈ᵢ 0`. -/
theorem PolyLevelSet.mem_relax_iff (P : PolyLevelSet n) (s : Vec ℝ P.m)
    (D : Interval (Vec ℝ P.m)) (x : Vec ℝ (n + P.m)) : -- --- CONCL ---
    x ∈ (P.relax s D).construct
      ↔ ((fun k => x (Fin.castAdd P.m k)) ∈ P.dom.construct
        ∧ (fun i => x (Fin.natAdd n i)) ∈ D.construct)
        ∧ ∀ i, (P.op i).holds
          (P.eval (fun k => x (Fin.castAdd P.m k)) i
            + s i * x (Fin.natAdd n i)) := by -- --- PROOF ---
  show (x ∈ (P.dom.append D).construct ∧ ∀ i, (P.op i).holds ((P.relax s D).eval x i)) ↔ _
  rw [Interval.mem_append_iff]
  refine and_congr Iff.rfl (forall_congr' fun i => ?_)
  rw [PolyLevelSet.aux_eval_relax]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
