module

public import CORALean.HybridDynamics.Definitions.NonlinearResetFloatModel
public import CORALean.HybridDynamics.Definitions.ResolveSource
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# `NonlinearReset.resolve` for a float model

CORA's `nonlinearReset/resolve` on interval extensions: the product reset reads the stacked input
of all components; input `col` is the global input it is bound to or the `l`-th output of the
component it is bound to, which is that component's interval extension at the boxes of its states
and of its globally bound inputs (a locally bound one is the origin, as in the real `resolve`). It
places existing bounds, so no rounding enters beyond the extensions'. CORA numbers the global
inputs differently, see `NonlinearReset.resolveCORA` and FINDINGS.md.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {N g k : ℕ} {n m p : Fin k → ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def NonlinearReset.FloatModel.resolve (fm : NonlinearReset.FloatModel 𝕋 N (∑ i, m i) N)
    (fmOut : ∀ i, Interval (Vec 𝕋 (n i)) → Interval (Vec 𝕋 (m i)) → Interval (Vec 𝕋 (p i)))
    (stateBinds : ∀ i, Fin (n i) → Fin N) (inputBinds : ∀ i, Fin (m i) → ResolveSource k p g) :
    NonlinearReset.FloatModel 𝕋 N g N where
  f := fun X V =>
    -- the box of component `c`'s states
    let Xc : ∀ c, Interval (Vec 𝕋 (n c)) := fun c =>
      ⟨fun s => X.inf (stateBinds c s), fun s => X.sup (stateBinds c s)⟩
    -- the box of component `c`'s input: its globally bound entries
    let Uc : ∀ c, Interval (Vec 𝕋 (m c)) := fun c =>
      ⟨fun jj => match inputBinds c jj with
        | .global a => V.inf a
        | .output _ _ => zero,
       fun jj => match inputBinds c jj with
        | .global a => V.sup a
        | .output _ _ => zero⟩
    -- the stacked input: the global input, or the output it is bound to
    fm.f X
      ⟨fun col => match inputBinds (finSigmaFinEquiv.symm col).1 (finSigmaFinEquiv.symm col).2 with
        | .global a => V.inf a
        | .output c l => (fmOut c (Xc c) (Uc c)).inf l,
       fun col => match inputBinds (finSigmaFinEquiv.symm col).1 (finSigmaFinEquiv.symm col).2 with
        | .global a => V.sup a
        | .output c l => (fmOut c (Xc c) (Uc c)).sup l⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
