module

public import CORALean.ContSet.PolyZonotope.Real.Theorems.BilinPoint
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MapPoint
public import CORALean.NN.Graph.Operations.GcnShared
public import CORALean.NN.Graph.Theorems.MatMulBilinApply

@[expose] public section

/-!
# A shared-factor convolution, at one factor vector

`gcnShared` is `bilin` and then `map`, so its point is `bilin_point` and then
`map_point`: at the factor vector `a` the step is the plain matrix product
`P.point a * H.point a * W`.

Read over `point` rather than over `construct` because a *chain* of steps is:
the recursion carries one factor vector from step to step, and it is that one
vector reaching every step which keeps a recurring edge identified. `Fin.cast`
is the whole bookkeeping — the two sets share a factor set, so the cast is the
identity, and only the proof it carries differs from use to use.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N F₁ F₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- One shared-factor convolution at a factor vector is the matrix product the
two sets take there, times the weight. -/
theorem GNN.gcnShared_point (W : Mat ℝ F₁ F₂) (P : PolyZonotope (Mat ℝ N N))
    (H : PolyZonotope (Mat ℝ N F₁)) (hp : P.p = H.p) (a : Fin P.p → ℝ) :
    (GNN.gcnShared W P H hp).point a
      = P.point a * H.point (fun k => a (Fin.cast hp.symm k)) * W := by -- --- PROOF ---
  have h := PolyZonotope.map_point (matMulRight W)
    (P.bilin (GNN.matMulBilin N N F₁) H hp) a
  -- the pairing is `bilin`, the known weight on the right is `map`
  rw [PolyZonotope.bilin_point, GNN.matMulBilin_apply] at h
  exact h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
