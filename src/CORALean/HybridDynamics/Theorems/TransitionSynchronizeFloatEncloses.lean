import CORALean.HybridDynamics.Operations.TransitionSynchronizeFloat
import CORALean.HybridDynamics.Theorems.LinearResetSynchronizeApply
import CORALean.HybridDynamics.Theorems.LinearResetSynchronizeFloatOuter
import CORALean.HybridDynamics.Theorems.LinearResetSynchronizeFloatOffsetOuter
import CORALean.HybridDynamics.Theorems.TransitionSynchronizeGuardExact

/-!
# The float `synchronize` encloses the synchronized transition

`Transition.synchronizeFloat` denotes, with equality, the intersection of the guards and the
target tuple of `Transition.synchronizeTarget`. Its interval reset contains a real reset
`x ↦ W x + w` (the real `LinearReset.synchronize` of the stored coefficients) that is, at every
point, the sum of the component resets plus the pre-jump value at `idStates`, which is what the
real `Transition.synchronize_reset` says the synchronized reset is. Outer in the reset only.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix CORALean.Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q k : ℕ} {L : Fin k → Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Transition.synchronizeFloat_encloses (compIdx : Fin q → Fin k)
    (t : ∀ i : Fin q, Transition (fun k => HPolytope 𝕋 (Vec 𝕋 k)) (L (compIdx i)) 𝕋 n)
    (idStates : Finset (Fin n)) (locID : ∀ c, L c) :
    let T := Transition.synchronizeFloat compIdx t idStates locID
    T.guard.construct = ⋂ i, (t i).guard.construct ∧
      T.target = Transition.synchronizeTarget locID compIdx (fun i => (t i).target) ∧
      ∃ (W : Mat ℝ n n) (w : Vec ℝ n),
        (∀ a b, toReal (T.W a b).inf ≤ W a b ∧ W a b ≤ toReal (T.W a b).sup) ∧
        (∀ a, toReal (T.w a).inf ≤ w a ∧ w a ≤ toReal (T.w a).sup) ∧
        ∀ x a, (W *ᵥ x + w) a =
          (if a ∈ idStates then x a else 0) + ∑ j, (t j).reset x a := by -- --- PROOF ---
  intro T
  -- the guard and the target are the real steps; the witness is the real reset sum
  refine ⟨Transition.synchronizeGuard_exact _, rfl,
    (LinearReset.synchronize (toRealMat ∘ fun i => (t i).W) (toRealVec ∘ fun i => (t i).w)
      idStates).1,
    (LinearReset.synchronize (toRealMat ∘ fun i => (t i).W) (toRealVec ∘ fun i => (t i).w)
      idStates).2,
    fun a b => LinearReset.synchronizeFloat_outer _ _ idStates a b,
    fun a => LinearReset.synchronizeFloat_offset_outer _ _ idStates a,
    fun x a => LinearReset.synchronize_apply _ _ idStates x a⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
