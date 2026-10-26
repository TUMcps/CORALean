module

public import CORALean.Global.Float.TimeOrder
public import CORALean.Specification.FourValued.Operations.Basic
public import CORALean.Specification.FourValuedSignal.Operations.Basic
public import CORALean.Specification.OnlineAnalyzerNode.Operations.ApValue
public import CORALean.Specification.OnlineAnalyzerNode.Operations.ConflictsFloat
public import CORALean.Specification.OnlineAnalyzerNode.OnlineAnalyzerNode
public import CORALean.Specification.STLInterval.Operations.Infimum
public import CORALean.Specification.TentativeKleeneSignal.Operations.Observe

@[expose] public section

/-!
# Observing a set, over a float scalar

`observeSet(obj,set,interval,loc,tentative)` with time stamps in `𝕋`: the conflict with what was
already propagated is `conflictsFloat`, whose comparisons are exact, and the rest reads the
interval's bounds exactly, so the result read as reals is what `observeSet` does with the node and
interval read as reals (`observeSetFloat_toRealNode`). `none` where CORA throws.

## Inputs
* `eps` – machine epsilon
* `n` – leaf node
* `set` – observed set
* `interval` – observed time interval
* `loc` – location
* `tentative` – observation is tentative

## Output
* the node after the observation, or none where CORA throws
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

/-- `observeSet(obj,set,interval,loc,tentative)`. -/
def OnlineAnalyzerNode.observeSetFloat (eps : 𝕋) (n : OnlineAnalyzerNode 𝕋 (AtomicProposition S d))
    (set : S d) (interval : STLInterval 𝕋) (loc : ℕ) (tentative : Bool) :
    Option (OnlineAnalyzerNode 𝕋 (AtomicProposition S d)) :=
  -- if ~ismember(obj.type,{'true','false','AP'}), throw notSupported
  if n.kind ≠ .true ∧ n.kind ≠ .false ∧ n.kind ≠ .ap then none
  else
    -- [lb,lc] = infimum(interval); for each prop(i): throw specialError if already propagated
    (OnlineAnalyzerNode.conflictsFloat eps interval.infimum.value interval.infimum.closed
      n.prop).bind fun bad =>
        if bad = true then none
        else
          match n.kind with
          -- case {'true','false'}: do nothing, as the signal is already properly initialized
          | .true | .false => some n
          | .ap =>
            -- canBeTrue, canBeFalse and val
            n.ap.bind fun ap => (OnlineAnalyzerNode.apValue (𝕋 := 𝕋) ap set loc).bind fun val =>
              if tentative = true then
                -- store the observation for later
                n.tentative.map fun tent => { n with tentative := some (tent.observe interval val) }
              else
                -- immediately update the satisfaction signal
                some { n with signal := n.signal.set interval (FourValued.fromKleene val) }
          | _ => none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
