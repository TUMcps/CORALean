import CORALean.ContDynamics.LinearSys.LinearSys

/-!
# Canonical form of a linear system

CORA's `isCanonicalForm` [1] asks whether `x' = Ax + B u + c + E w`, `y = Cx + D u + k + F v`
is `x' = Ax + u`, `y = Cx + v`: as many inputs as states (`m = n`) with `B = I`, as many
noises as outputs (`s = r`), and `c`, `k`, `E`, `D` zero. `C` is left free, as the docstring
(`y = Cx + v`) and `canonicalForm`'s own output have it; CORA's code also tests
`C == eye(nrOfOutputs)`, see FINDINGS.md.

## References

* [1] `contDynamics/@linearSys/isCanonicalForm.m`
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m q r s : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Prop-valued, as `Isequal` is: the entries are real numbers. -/
def LinearSys.IsCanonicalForm (B : Mat ℝ n m) (c : Vec ℝ n) (D : Mat ℝ r m) (k : Vec ℝ r)
    (E : Mat ℝ n q) (_F : Mat ℝ r s) : Prop :=
  m = n ∧ s = r ∧ c = 0 ∧ k = 0 ∧ E = 0 ∧ D = 0 ∧
    ∀ i j, B i j = if (i : ℕ) = (j : ℕ) then 1 else 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
