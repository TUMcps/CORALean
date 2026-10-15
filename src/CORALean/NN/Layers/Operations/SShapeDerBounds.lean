module

public import CORALean.NN.Layers.Definitions.IsSShape
public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# `nnSShapeLayer.getDerBounds`

CORA's `getDerBounds`: the least and greatest derivative of an S-shaped activation over `[l, u]`.
Its maximum is `df 0` when `0` lies inside and `df` at the nearer end otherwise; its minimum is
`df` at the end farther from `0`. Not modelled: the `NaN` fallback `(0, 0.0001)`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type} [AddCommGroup α] [LinearOrder α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The bounds `(df_l, df_u)` on `df` over `[l, u]`, by CORA's three cases. -/
def sShapeDerBounds (df : α → α) (l u : α) : Real.Interval α :=
  if l ≤ 0 ∧ 0 ≤ u then ⟨if -l ≥ u then df l else df u, df 0⟩   -- `0` inside: peak at `0`
  else if 0 < l then ⟨df u, df l⟩                                  -- right of `0`: decreasing
  else ⟨df l, df u⟩                                                -- left of `0`: increasing

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
