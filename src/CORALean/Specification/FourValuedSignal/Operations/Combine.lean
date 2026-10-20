module

public import CORALean.Specification.FourValuedSignal.FourValuedSignal
public import CORALean.Specification.KleeneSignal.Operations.Combine
public import CORALean.Specification.KleeneSignal.Operations.Basic
public import CORALean.Specification.FourValued.Operations.Basic
public import CORALean.Specification.Kleene.Operations.Basic

@[expose] public section

/-!
# Point-wise combination of four-valued signals

`combine(op,varargin)` of `fourValuedSignal.m`: the point-wise combination of `kleeneSignal.combine`
over the Kleene parts of the inputs and their inconclusive parts (as Kleene signals), with `op`
acting on four-valued values. Each output is its Kleene part and its inconclusive flag (a Kleene
value, converted back by `toBoolSignal()`, which throws on unknown; `none` there gives the Kleene
part's signal).

Refinement pending: CORA computes this in doubles, and its refinement generic over `𝕋` (time
stamps over `𝕋`, rounded outward) is not yet written.

## Inputs
* `ι` – index type of the inputs
* `κ` – index type of the outputs
* `op` – pointwise operator on four-valued values
* `sig` – four-valued input signals

## Output
* the combined four-valued signals
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sigs = fourValuedSignal.combine(op,varargin)`. -/
noncomputable def FourValuedSignal.combine {ι κ : Type} [Fintype ι]
    (op : (ι → FourValued) → κ → FourValued) (sig : ι → FourValuedSignal ℝ) :
    κ → FourValuedSignal ℝ := fun i =>
  -- 1. c = [arr.signal,inconclusiveKleene], inconclusiveKleene = fromBoolSignal(s.isInconclusive)
  let c : ι ⊕ ι → KleeneSignal ℝ := Sum.elim (fun k => (sig k).signal)
    (fun k => KleeneSignal.fromBoolSignal (sig k).isInconclusive)
  -- 2. u2Op: join the parts of the inputs, apply `op`, split the outputs
  let u2Op : (ι ⊕ ι → Kleene) → κ × Bool → Kleene := fun args o =>
    let u2s := fun k => FourValued.ofKleeneInc (args (Sum.inl k)) (args (Sum.inr k)).toBool
    if o.2 then Kleene.fromBool (op u2s o.1).isInconclusive else (op u2s o.1).toKleene
  -- 3. pSigs = kleeneSignal.combine(@u2Op,c{:})
  let pSigs := KleeneSignal.combine u2Op c
  ⟨pSigs (i, false), ((pSigs (i, true)).toBoolSignal?).getD (pSigs (i, true)).signal⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
