import CORALean.HybridDynamics.Definitions.NonlinearReset
import CORALean.HybridDynamics.Definitions.ResolveSource
import Mathlib.Algebra.BigOperators.Fin
import CORALean.HybridDynamics.Operations.NonlinearResetGlobalColumns
import CORALean.HybridDynamics.Operations.NonlinearResetGlobalRank

/-!
# `NonlinearReset.resolveCORA`

`nonlinearReset/resolve` as CORA's code does it: the last step `subs(f_sym, u_sym(idxGlobalInput),
u_sym(1:numGlobalInputs))` numbers the globally bound inputs `1, 2, ...` in the order they occur
and ignores the global index they are bound to (FINDINGS.md).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {N g k : ℕ} {n m p : Fin k → ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def NonlinearReset.resolveCORA (r : NonlinearReset N (∑ i, m i) N)
    (out : ∀ i, Vec ℝ (n i) → Vec ℝ (m i) → Vec ℝ (p i))
    (stateBinds : ∀ i, Fin (n i) → Fin N) (inputBinds : ∀ i, Fin (m i) → ResolveSource k p g) :
    NonlinearReset N (NonlinearReset.globalColumns inputBinds) N where
  f := fun x v =>
    -- `u_sym(idxGlobalInput) -> u_sym(1:numGlobalInputs)`: the global input of an input is its rank
    let vOf : (Σ i, Fin (m i)) → ℝ := fun ij =>
      if h : NonlinearReset.globalRank inputBinds ij < NonlinearReset.globalColumns inputBinds
      then v ⟨NonlinearReset.globalRank inputBinds ij, h⟩ else 0
    let xc : ∀ c, Vec ℝ (n c) := fun c s => x (stateBinds c s)
    let uc : ∀ c, Vec ℝ (m c) := fun c jj =>
      match inputBinds c jj with
      | .global _ => vOf ⟨c, jj⟩
      | .output _ _ => 0
    let uSub : Vec ℝ (∑ i, m i) := fun col =>
      match inputBinds (finSigmaFinEquiv.symm col).1 (finSigmaFinEquiv.symm col).2 with
      | .global _ => vOf (finSigmaFinEquiv.symm col)
      | .output c l => out c (xc c) (uc c) l
    r.f x uSub

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
