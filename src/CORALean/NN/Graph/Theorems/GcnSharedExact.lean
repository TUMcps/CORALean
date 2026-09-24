import CORALean.ContSet.PolyZonotope.Real.Theorems.BilinExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.MapExact
import CORALean.NN.Graph.Operations.GcnShared

/-!
# A shared-factor convolution loses nothing

An equality, as `gcnUncertain_exact` is, and for the same reason: `bilin` is
exact at a shared factor set and `map` is exact at a linear one, so the step
itself gives nothing away. What is new is only that the two sets are *not*
padded apart — the pairing runs over factors they already had in common, which
is what a second step at the same graph needs.

Stated over `point`, so `H`'s independent block takes no part: `bilin` drops it
by construction, and a caller who needs it accounted for runs
`PolyZonotope.dependent` first, exactly as the message-passing enclosure does.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N F₁ F₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A shared-factor convolution is exactly the set of products the two sets take
at a common factor vector. -/
theorem GNN.gcnShared_exact (W : Mat ℝ F₁ F₂) (P : PolyZonotope (Mat ℝ N N))
    (H : PolyZonotope (Mat ℝ N F₁)) (hp : P.p = H.p) :
    (fun a : Fin P.p → ℝ => P.point a * H.point (fun k => a (Fin.cast hp.symm k)) * W)
        '' {a | ∀ k, |a k| ≤ 1}
      = (GNN.gcnShared W P H hp).construct := by -- --- PROOF ---
  have hb := PolyZonotope.bilin_exact (GNN.matMulBilin N N F₁) P H hp
  have hm := PolyZonotope.map_exact (matMulRight W) (P.bilin (GNN.matMulBilin N N F₁) H hp)
  -- the step is the pairing and then the weight, so the two images compose
  rw [GNN.gcnShared, ← hm, ← hb, ← Set.image_comp]
  exact Set.image_congr' fun _ => rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
