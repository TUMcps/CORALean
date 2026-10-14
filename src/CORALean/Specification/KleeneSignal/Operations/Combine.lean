module

public import CORALean.Specification.KleeneSignal.KleeneSignal
public import CORALean.Specification.PointSegmentSignal.Operations.Combine
public import CORALean.Specification.Kleene.Operations.Basic

@[expose] public section

/-!
# Point-wise combination of three-valued signals

`combine(op,varargin)` of `kleeneSignal.m`: the point-wise combination of
`pointSegmentSignal.combine` over the Boolean parts and unknown parts of the inputs, with `op`
acting on Kleene values. Each Kleene output is returned as its Boolean and unknown part, which are
two outputs of the underlying combination.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sigs = kleeneSignal.combine(op,varargin)`. -/
def KleeneSignal.combine {T : Type} [LinearOrder T] [Zero T] {ι κ : Type} [Fintype ι]
    (op : (ι → Kleene) → κ → Kleene) (sig : ι → KleeneSignal T) : κ → KleeneSignal T := fun i =>
  -- 1. c = [arr.signal,arr.isUnknown]
  let c : ι ⊕ ι → PointSegmentSignal T :=
    Sum.elim (fun k => (sig k).signal) (fun k => (sig k).isUnknown)
  -- 2. kOp: join the parts of the inputs, apply `op`, split the outputs
  let kOp : (ι ⊕ ι → Bool) → κ × Bool → Bool := fun args o =>
    let kleenes := fun k => Kleene.ofBoolUnk (args (Sum.inl k)) (args (Sum.inr k))
    if o.2 then (op kleenes o.1).isUnknown else (op kleenes o.1).toBool
  -- 3. pSigs = pointSegmentSignal.combine(@kOp,c{:})
  let pSigs := PointSegmentSignal.combine kOp c
  ⟨pSigs (i, false), pSigs (i, true)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
