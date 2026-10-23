module

public import CORALean.ContSet.PolyLevelSet.Real.Operations.Linear
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialIdentE

@[expose] public section

/-!
# What `PolyLevelSet.linear` denotes

The points meeting every row `(A x - b)ᵢ ⋈ᵢ 0`: monomial `k` of `identE` is `xₖ`
(`PolyZonotope.monomial_identE`), so the polynomial part is `A x`.

## Inputs
* `m` – number of rows
* `A` – coefficient matrix
* `b` – right-hand side
* `op` – comparison of each row
* `D` – box of the variables
* `x` – point

## Hypotheses
* none

## Conclusion
* `x` lies in the set iff it lies in the box and meets each row
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A point of the linear level set is in the box and meets every row `(A x - b)ᵢ ⋈ᵢ 0`. -/
theorem PolyLevelSet.mem_linear_iff {m : ℕ} (A : Mat ℝ m n) (b : Vec ℝ m)
    (op : Fin m → CompOp) (D : Interval (Vec ℝ n)) (x : Vec ℝ n) : -- --- CONCL ---
    x ∈ (PolyLevelSet.linear A b op D).construct
      ↔ x ∈ D.construct ∧ ∀ i, (op i).holds ((A *ᵥ x - b) i) := by -- --- PROOF ---
  have hμ : PolyZonotope.monomial (PolyZonotope.identE n) x = x :=
    funext fun k => PolyZonotope.monomial_identE x k
  show (x ∈ D.construct
    ∧ ∀ i, (op i).holds ((A *ᵥ PolyZonotope.monomial (PolyZonotope.identE n) x - b) i)) ↔ _
  rw [hμ]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
