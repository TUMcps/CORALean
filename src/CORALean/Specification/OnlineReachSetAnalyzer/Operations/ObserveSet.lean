module

public import CORALean.Specification.OnlineAnalyzerNode.Operations.ObserveSet
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.Basic
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.Propagate

@[expose] public section

/-!
# Observing a set

`observeSet(obj,set,interval,loc,makeValid)`: the reachable set `set` at location `loc` is reached
in `interval`. An empty interval changes nothing. Without `makeValid` the observation is final
(`tentative = false`), with it only the times of `makeValid` are made final later by the
propagation. Every leaf node observes the set, the observation is counted, and every
`propagationFrequency`-th observation triggers the propagation. CORA converts a `zonoBundle`
to a zonotope first (a change of the representation `S`, left to the caller) and throws where a leaf
does (every throw is `none`). `eps` is MATLAB's `eps`.

## Inputs
* `eps` – machine epsilon
* `obj` – analyzer
* `set` – reachable set
* `interval` – time interval of the set
* `loc` – location
* `makeValid` – interval to make final

## Output
* the analyzer after the observation, or none where CORA throws
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type} {d : ℕ}
  [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `observeSet(obj,set,interval,loc,makeValid)`. -/
noncomputable def OnlineReachSetAnalyzer.observeSet (eps : ℝ) (obj : OnlineReachSetAnalyzer S d)
    (set : S d) (interval : STLInterval) (loc : ℕ) (makeValid : Option STLInterval := none) :
    Option (OnlineReachSetAnalyzer S d) :=
  match interval with
  -- if the interval is empty, we cannot do anything with this observation
  | .empty => some obj
  | .nonempty .. =>
    -- if nargin < 5: tentative = false; makeValid = stlInterval(); else tentative = true
    let tentative := makeValid.isSome
    let makeValid := makeValid.getD .empty
    -- add the new observation to the leaves
    (obj.leaves.foldlM (fun nodes l => OnlineReachSetAnalyzer.updateNode nodes l fun n =>
      OnlineAnalyzerNode.observeSet (𝕋 := 𝕋) eps n set interval loc tentative) obj.nodes).bind
      fun nodes =>
        -- obj.numObservations = obj.numObservations + 1
        let obj' := { obj with nodes := nodes, numObservations := obj.numObservations + 1 }
        -- trigger the propagation if necessary
        if obj'.numObservations % obj'.propagationFrequency = 0 then obj'.propagate eps makeValid
        else some obj'

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
