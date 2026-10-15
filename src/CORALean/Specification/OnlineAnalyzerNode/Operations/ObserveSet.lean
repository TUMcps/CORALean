module

public import CORALean.Specification.FourValued.Operations.Basic
public import CORALean.Specification.FourValuedSignal.Operations.Basic
public import CORALean.Specification.OnlineAnalyzerNode.Operations.ApValue
public import CORALean.Specification.OnlineAnalyzerNode.Operations.Conflicts
public import CORALean.Specification.OnlineAnalyzerNode.OnlineAnalyzerNode
public import CORALean.Specification.TentativeKleeneSignal.Operations.Observe

@[expose] public section

/-!
# Observing a set

`observeSet(obj,set,interval,loc,tentative)` of `onlineAnalyzerNode.m`: a leaf node (`true`,
`false`, `AP`) observes that the reachable set `set` at the location `loc` is reached in
`interval`. CORA throws `CORA:notSupported` for other nodes and `CORA:specialError` for an
observation of a time that was already propagated; a `true` or `false` node does nothing more;
an `AP` node derives the value of its proposition on the set (`apValue`) and either stores it for
later in its tentative signal (`tentative`) or sets its satisfaction signal on the interval. Every
throw is `none` here, and so is a node of kind `AP` without proposition or tentative signal.
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

/-- `observeSet(obj,set,interval,loc,tentative)`. -/
noncomputable def OnlineAnalyzerNode.observeSet (eps : ℝ)
    (n : OnlineAnalyzerNode (AtomicProposition S d)) (set : S d) (interval : STLInterval)
    (loc : ℕ) (tentative : Bool) : Option (OnlineAnalyzerNode (AtomicProposition S d)) :=
  -- if ~ismember(obj.type,{'true','false','AP'}), throw notSupported
  if n.kind ≠ .true ∧ n.kind ≠ .false ∧ n.kind ≠ .ap then none
  else
    -- [lb,lc] = infimum(interval); for each prop(i): throw specialError if already propagated
    (OnlineAnalyzerNode.conflicts eps interval.infimum.value interval.infimum.closed n.prop).bind
      fun bad =>
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
