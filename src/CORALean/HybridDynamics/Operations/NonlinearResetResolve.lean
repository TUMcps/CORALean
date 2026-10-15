module

public import CORALean.HybridDynamics.Definitions.NonlinearReset
public import CORALean.HybridDynamics.Definitions.ResolveSource
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# `NonlinearReset.resolve`

CORA's `nonlinearReset/resolve`: the reset `f(x, u)` of a parallel automaton, whose input `u`
stacks the inputs of all `k` components, as a reset of the global input `v` only. Every input `j`
of component `i` bound to the `l`-th output `y_c(x_c, u_c)` of component `c` is substituted by it,
where `u_c` is `c`'s input, of which only the globally bound entries may enter (CORA throws if the
output depends on a locally bound one), and a globally bound input is the global input it is bound
to: input `a` of the product is `v a`. CORA numbers the global inputs differently, see
`NonlinearReset.resolveCORA` and `references/coverage/hybridDynamics/nonlinearReset.md`, row
`resolve`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {N g k : ℕ} {n m p : Fin k → ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def NonlinearReset.resolve (r : NonlinearReset N (∑ i, m i) N)
    (out : ∀ i, Vec ℝ (n i) → Vec ℝ (m i) → Vec ℝ (p i))
    (stateBinds : ∀ i, Fin (n i) → Fin N) (inputBinds : ∀ i, Fin (m i) → ResolveSource k p g) :
    NonlinearReset N g N where
  f := fun x v =>
    -- `x_sym(stateBinds{c})`
    let xc : ∀ c, Vec ℝ (n c) := fun c s => x (stateBinds c s)
    -- the input of component `c`: its globally bound entries
    let uc : ∀ c, Vec ℝ (m c) := fun c jj =>
      match inputBinds c jj with
      | .global a => v a
      | .output _ _ => 0
    -- `f_sym = subs(f_sym, u_sym(idxCompInput{i}(:,j)), g_otherComp_sym_l)`: input `col`
    let uSub : Vec ℝ (∑ i, m i) := fun col =>
      match inputBinds (finSigmaFinEquiv.symm col).1 (finSigmaFinEquiv.symm col).2 with
      | .global a => v a
      | .output c l => out c (xc c) (uc c) l
    r.f x uSub

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
