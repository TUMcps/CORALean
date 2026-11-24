module

public import CORALean.NN.Operations.HeldChainBackprop
public import CORALean.NN.Operations.HeldChainBackpropFloat
public import CORALean.NN.Definitions.HeldChainFloatEncloses
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MtimesMem
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint

@[expose] public section

/-!
# The float held backpropagation encloses the real one

For a float held chain `c` that stands for the real chain `r` (`HeldChain.Encloses`) and an output
gradient `g` in the box `G`, the real `HeldChain.backprop` lies in the box the float one returns:
each linear layer's `Wᵀ g` by `Interval.mtimes`, each slope layer's `s ⊙ g` by `Interval.times`.

## Inputs
* `n` – input width
* `k` – output width
* `c` – float held chain
* `r` – real held chain
* `G` – float box of the output gradient
* `g` – real output gradient

## Hypotheses
* `hc` – the float chain stands for the real chain
* `hg` – the gradient lies in its box

## Conclusion
* the real backpropagation lies in the float box
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HeldChain.backprop_outer {n k : ℕ} {c : HeldChain 𝕋 n k} {r : Real.HeldChain n k}
    (hc : c.Encloses r) (G : Interval (Vec 𝕋 k)) {g : Vec ℝ k} (hg : g ∈ G.toSet) : -- --- CONCL ---
    r.backprop g ∈ (c.backprop G).toSet := by -- --- PROOF ---
  induction hc with
  | nil => exact hg
  | @linear n m k W c r _ ih =>
    -- the transposed map of the rest's box
    show _ ∈ (Interval.materialise _).toSet
    rw [Interval.materialise_eq]
    exact Interval.mtimes_mem Wᵀ (toRealMat W)ᵀ rfl _ (ih G hg)
  | @slope n k s c r _ ih =>
    -- the slopes' point box times the rest's box
    show _ ∈ (Interval.materialise _).toSet
    rw [Interval.materialise_eq]
    exact Interval.times_outer _ _ ⟨toRealVec s, Interval.mem_point s, _, ih G hg, rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
