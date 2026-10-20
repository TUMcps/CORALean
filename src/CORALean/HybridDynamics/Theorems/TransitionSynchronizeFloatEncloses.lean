module

public import CORALean.HybridDynamics.Operations.TransitionSynchronizeFloat
public import CORALean.HybridDynamics.Theorems.LinearResetSynchronizeApply
public import CORALean.HybridDynamics.Theorems.LinearResetSynchronizeFloatOuter
public import CORALean.HybridDynamics.Theorems.LinearResetSynchronizeFloatOffsetOuter
public import CORALean.HybridDynamics.Theorems.TransitionSynchronizeGuardOuter

@[expose] public section

/-!
# The float `synchronize` encloses the synchronized transition

`Transition.synchronizeFloat` has a guard containing the intersection of the guards, and the
target tuple of `Transition.synchronizeTarget`. Its interval reset contains a real reset
`x ↦ W x + w` (the real `LinearReset.synchronize` of the stored coefficients) that is, at every
point, the sum of the component resets plus the pre-jump value at `idStates`, which is what the
real `Transition.synchronize_reset` says the synchronized reset is. Outer in the reset only.

## Inputs
* `compIdx` – component indices
* `t` – transitions of the components
* `idStates` – states kept by identity
* `locID` – current locations

## Hypotheses
* none

## Conclusion
* the synchronized float transition encloses the synchronized transition
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       12-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix CORALean.Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q k : ℕ} {L : Fin k → Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Transition.synchronizeFloat_encloses (compIdx : Fin q → Fin k)
    (t : ∀ i : Fin q, Transition (fun k => HPolytope 𝕋 (Vec 𝕋 k)) (L (compIdx i)) 𝕋 n)
    (idStates : Finset (Fin n)) (locID : ∀ c, L c) : -- --- CONCL ---
    let T := Transition.synchronizeFloat compIdx t idStates locID
    ⋂ i, (t i).guard.construct ⊆ T.guard.construct ∧
      T.target = Transition.synchronizeTarget locID compIdx (fun i => (t i).target) ∧
      ∃ (W : Mat ℝ n n) (w : Vec ℝ n),
        (∀ a b, toReal (T.W a b).inf ≤ W a b ∧ W a b ≤ toReal (T.W a b).sup) ∧
        (∀ a, toReal (T.w a).inf ≤ w a ∧ w a ≤ toReal (T.w a).sup) ∧
        ∀ x a, (W *ᵥ x + w) a =
          (if a ∈ idStates then x a else 0) + ∑ j, (t j).reset x a := by -- --- PROOF ---
  intro T
  -- the guard and the target are the real steps; the witness is the real reset sum
  refine ⟨Transition.synchronizeGuard_outer _, rfl,
    (LinearReset.synchronize (toRealMat ∘ fun i => (t i).W) (toRealVec ∘ fun i => (t i).w)
      idStates).1,
    (LinearReset.synchronize (toRealMat ∘ fun i => (t i).W) (toRealVec ∘ fun i => (t i).w)
      idStates).2,
    fun a b => LinearReset.synchronizeFloat_outer _ _ idStates a b,
    fun a => LinearReset.synchronizeFloat_offset_outer _ _ idStates a,
    fun x a => LinearReset.synchronize_apply _ _ idStates x a⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
