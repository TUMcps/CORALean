module

public import CORALean.ContDynamics.LinearSys.LinearSys

@[expose] public section

/-!
# Canonical form of a linear system

CORA's `isCanonicalForm` [1] asks whether `x' = Ax + B u + c + E w`, `y = Cx + D u + k + F v`
is `x' = Ax + u`, `y = Cx + v`: as many inputs as states (`m = n`) with `B = I`, as many
noises as outputs (`s = q`), and `c`, `k`, `E`, `D` zero, at the real values the entries
denote. `C` is left free, as the docstring (`y = Cx + v`) and `canonicalForm`'s own output have
it; CORA's code also tests `C == eye(nrOfOutputs)`, see FINDINGS.md.

## References

* [1] `contDynamics/@linearSys/isCanonicalForm.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Prop-valued, as `Isequal` is: the entries are read as real numbers. -/
def LinearSys.IsCanonicalForm (sys : LinearSys 𝕋 n) : Prop :=
  sys.m = n ∧ sys.s = sys.q ∧ toRealVec sys.c = 0 ∧ toRealVec sys.k = 0 ∧ toRealMat sys.E = 0 ∧
    toRealMat sys.D = 0 ∧ ∀ i j, toRealMat sys.B i j = if (i : ℕ) = (j : ℕ) then 1 else 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
