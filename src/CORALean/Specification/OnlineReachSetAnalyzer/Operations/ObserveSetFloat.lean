module

public import CORALean.Specification.OnlineAnalyzerNode.Operations.ObserveSetFloat
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.Basic
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.PropagateFloat

@[expose] public section

/-!
# Observing a set, over a float scalar

`observeSet(obj,set,interval,loc,makeValid)` with time stamps in `𝕋`: every leaf observes the set
by `OnlineAnalyzerNode.observeSetFloat`, the observation is counted, and the propagation, if due,
is `propagateFloat`. Over a whole run its `True` and `False` verdicts are those of `observeSet`
(`observeSetFloat_sound`).

## Inputs
* `eps` – machine epsilon
* `obj` – analyzer
* `set` – observed set
* `interval` – observed time interval
* `loc` – location
* `makeValid` – interval to make final, if the observation is tentative

## Output
* the analyzer after the observation, or none where CORA throws
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋] [Scalar 𝕋]
  [ExactScalar 𝕋] {S : ℕ → Type} {d : ℕ} [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S]
  [∀ k, Contains (S k) (S k)] [∀ k, IsDisjoint (S k) (S k)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `observeSet(obj,set,interval,loc,makeValid)`. -/
def OnlineReachSetAnalyzer.observeSetFloat (eps : 𝕋) (obj : OnlineReachSetAnalyzer 𝕋 S d)
    (set : S d) (interval : STLInterval 𝕋) (loc : ℕ) (makeValid : Option (STLInterval 𝕋) := none) :
    Option (OnlineReachSetAnalyzer 𝕋 S d) :=
  match interval with
  -- if the interval is empty, we cannot do anything with this observation
  | .empty => some obj
  | .nonempty .. =>
    -- if nargin < 5: tentative = false; makeValid = stlInterval(); else tentative = true
    let tentative := makeValid.isSome
    let makeValid := makeValid.getD .empty
    -- add the new observation to the leaves
    (obj.leaves.foldlM (fun nodes l => OnlineReachSetAnalyzer.updateNode nodes l fun n =>
      OnlineAnalyzerNode.observeSetFloat eps n set interval loc tentative) obj.nodes).bind
      fun nodes =>
        -- obj.numObservations = obj.numObservations + 1
        let obj' := { obj with nodes := nodes, numObservations := obj.numObservations + 1 }
        -- trigger the propagation if necessary
        if obj'.numObservations % obj'.propagationFrequency = 0 then
          obj'.propagateFloat eps makeValid
        else some obj'

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
