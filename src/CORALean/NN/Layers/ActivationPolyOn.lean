import CORALean.NN.Layers.ActivationPoly

/-!
# The polynomial activation layer, fitted on a box it is handed

`Layer.activationPoly` fits each neuron on the box of the set in front of it.
This fits them on a box `J` supplied from outside — [1, Prop. 4.2], where the
box a later iteration uses is `Interval.intersection` of the boxes earlier
iterations computed, each of which already contained the exact set.

What survives is pointwise soundness and not `Layer.Sound`: `J` answers for the
points it contains and for no others, so the claim is at a point of the input
set that `J` holds too. That is what the loop has — the enclosure is sound for
the exact set even where it says nothing about the set this iteration computed.

The fit's own error carries it: `sound` bounds `|σ t - p t|` between `J`'s ends,
and `t` is the input point, so `J` never has to contain the whole set.

`Real` only, and the reason is that nothing here rounds: what changes is which
box the fits are read at, while the float layer's arithmetic lives in its own
`evalPoly` and in the fit, neither of which this substitution touches.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       12-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise ContSet Plus

variable {σ : ℝ → ℝ} {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The activation layer at a box handed to it: every fit and the residual box
read `J`, so nothing here depends on the set being enclosed. -/
noncomputable def Layer.activationPolyOn (P : LayerRelaxation σ n m) (J : Interval (Vec ℝ n)) :
    Layer 𝒫𝒵 n n where
  enclose s := plus (s.dependent.evalPoly (P.coeffList J)) (Interval.polyZonotope (P.box J))

theorem Layer.activationPolyOn_outer (P : LayerRelaxation σ n m) (J : Interval (Vec ℝ n))
    (s : 𝒫𝒵 n) {x : Vec ℝ n} (hx : x ∈ construct s) (hJ : x ∈ J.construct) :
    (fun i => σ (x i)) ∈ construct ((Layer.activationPolyOn P J).enclose s) := by -- --- PROOF ---
  have hxd : x ∈ s.dependent.construct := by
    rw [← PolyZonotope.dependent_exact s]
    exact hx
  obtain ⟨a, ha, hxa⟩ := s.dependent.exists_point_of_q_zero rfl hxd
  -- the polynomial part, read at the very factors `x` itself came from
  have hpval : (s.dependent.evalPoly (P.coeffList J)).point
        (fun k => a (Fin.cast (s.dependent.evalPoly_p (P.coeffList J)) k))
      = fun i => evalPoly ((P i).coeffs (J.inf i) (J.sup i)) (x i) := by
    rw [PolyZonotope.evalPoly_exact]
    funext i
    rw [LayerRelaxation.coeffList_coord, PolyZonotope.evalPolyReal_ofFn, ← congrFun hxa i]
    rfl
  have hpmem : (fun i => evalPoly ((P i).coeffs (J.inf i) (J.sup i)) (x i))
      ∈ (s.dependent.evalPoly (P.coeffList J)).construct :=
    hpval ▸ PolyZonotope.point_mem_construct _ fun k => ha _
  -- `J` is asked for nothing but the two ends the fit was made between
  have hdev : (fun i => σ (x i) - evalPoly ((P i).coeffs (J.inf i) (J.sup i)) (x i))
      ∈ (P.box J).construct := by
    intro i
    have hrel := abs_le.mp ((P i).sound (hJ i).1 (hJ i).2)
    exact ⟨hrel.1, hrel.2⟩
  have hsplit : (fun i => σ (x i))
      = (fun i => evalPoly ((P i).coeffs (J.inf i) (J.sup i)) (x i))
        + fun i => σ (x i) - evalPoly ((P i).coeffs (J.inf i) (J.sup i)) (x i) := by
    funext i
    show σ (x i) = _ + _
    ring
  rw [hsplit]
  exact plus_outer _ _ (Set.add_mem_add hpmem (Interval.polyZonotope_contains _ hdev))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
