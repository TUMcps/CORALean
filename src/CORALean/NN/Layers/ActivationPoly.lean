import CORALean.ContSet.Conversion.Real.Interval_to_PolyZonotope
import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Interval
import CORALean.ContSet.PolyZonotope.Real.Instances
import CORALean.ContSet.PolyZonotope.Real.Theorems.DependentExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyRealOfFn
import CORALean.ContSet.PolyZonotope.Real.Theorems.ExistsPointOfQZero
import CORALean.ContSet.PolyZonotope.Real.Theorems.PointMemConstruct
import CORALean.NN.Layers.PolyRelaxation

/-!
# The activation layer at a polynomial relaxation

CORA's `evaluatePolyZonotopeNeuron` [1]: a fit of its own per neuron, at the
common degree `PolyRelaxationPad` brings them to, evaluated on the set through
`PolyZonotope.evalPoly` with only what the fits miss thrown into a box.
`Layer.activation` keeps a slope and boxes the rest; this keeps a degree-`m`
dependence on the input factors, which is the precision refinement spends.

Pinned to `PolyZonotope` rather than generic in `S`. `evalPoly` has no
counterpart at a general representation — no convex one is closed under it — so
a class carrying it would have a single implementor and say nothing, which is
the judgement `Real/Instances.lean` already records for `quadMap`. One
representation is the honest answer until a second one can implement it.

The independent block is not ignored: `evalPoly` takes no `dependent` wrapper,
since running one on each of two sets would identify unrelated uncertainties, so
this layer runs `dependent` once, on its own input. `exists_point_of_q_zero` is
then what carries the resulting factors to every member.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise ContSet Plus

variable {σ : ℝ → ℝ} {m n : ℕ}

/-- A layer's abstraction: one relaxation per neuron, all at one degree, which
is what an order pattern makes of a nonlinear layer [1, Eq. 23]. -/
abbrev LayerRelaxation (σ : ℝ → ℝ) (n m : ℕ) := Fin n → PolyRelaxation σ m

/-- Neuron `i`'s coefficient of `t ^ k`, from its own fit on its own input
range: one vector per degree, which is how `evalPoly` reads a coefficient. -/
def LayerRelaxation.coeffVec (P : LayerRelaxation σ n m) (I : Interval (Vec ℝ n))
    (k : Fin (m + 1)) : Vec ℝ n := fun i => (P i).coeffs (I.inf i) (I.sup i) k

/-- Those vectors as `PolyZonotope.evalPoly` takes them, lowest degree first. -/
def LayerRelaxation.coeffList (P : LayerRelaxation σ n m) (I : Interval (Vec ℝ n)) :
    List (Vec ℝ n) := List.ofFn (P.coeffVec I)

/-- Coordinate `i` of the list is neuron `i`'s own coefficients, which is what
makes one `evalPoly` call carry `n` different polynomials. -/
theorem LayerRelaxation.coeffList_coord (P : LayerRelaxation σ n m) (I : Interval (Vec ℝ n))
    (i : Fin n) : ((P.coeffList I).map fun v => v i)
      = List.ofFn ((P i).coeffs (I.inf i) (I.sup i)) := by
  rw [LayerRelaxation.coeffList, List.map_ofFn]
  rfl

/-- The box each neuron's deviation from its own polynomial is confined to.
Centred at zero, `sound` bounding an absolute value and nothing else. -/
def LayerRelaxation.box (P : LayerRelaxation σ n m) (I : Interval (Vec ℝ n)) :
    Interval (Vec ℝ n) where
  inf := fun i => -(P i).error (I.inf i) (I.sup i)
  sup := fun i => (P i).error (I.inf i) (I.sup i)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The activation layer of a layer's relaxation: `dependent` first, then each
neuron's fit on the set, then the residual box. -/
noncomputable def Layer.activationPoly (P : LayerRelaxation σ n m) : Layer 𝒫𝒵 n n where
  enclose s := plus (s.dependent.evalPoly (P.coeffList s.interval))
    (Interval.polyZonotope (P.box s.interval))

theorem Layer.activationPoly_sound (P : LayerRelaxation σ n m) :
    (Layer.activationPoly P).Sound (fun x i => σ (x i)) := by -- --- PROOF ---
  refine ⟨fun s x hx => ?_⟩
  have hbox := PolyZonotope.interval_contains s hx
  have hxd : x ∈ s.dependent.construct := by
    rw [← PolyZonotope.dependent_exact s]
    exact hx
  obtain ⟨a, ha, hxa⟩ := s.dependent.exists_point_of_q_zero rfl hxd
  -- the polynomial part, read at the very factors `x` itself came from
  have hpval : (s.dependent.evalPoly (P.coeffList s.interval)).point
        (fun k => a (Fin.cast (s.dependent.evalPoly_p (P.coeffList s.interval)) k))
      = fun i => evalPoly ((P i).coeffs (s.interval.inf i) (s.interval.sup i)) (x i) := by
    rw [PolyZonotope.evalPoly_exact]
    funext i
    rw [LayerRelaxation.coeffList_coord, PolyZonotope.evalPolyReal_ofFn, ← congrFun hxa i]
    rfl
  have hpmem : (fun i => evalPoly ((P i).coeffs (s.interval.inf i) (s.interval.sup i)) (x i))
      ∈ (s.dependent.evalPoly (P.coeffList s.interval)).construct :=
    hpval ▸ PolyZonotope.point_mem_construct _ fun k => ha _
  -- and the deviation from that polynomial is inside the box, which is `sound`
  have hdev : (fun i => σ (x i)
        - evalPoly ((P i).coeffs (s.interval.inf i) (s.interval.sup i)) (x i))
      ∈ (P.box s.interval).construct := by
    intro i
    have hrel := abs_le.mp ((P i).sound (hbox i).1 (hbox i).2)
    exact ⟨hrel.1, hrel.2⟩
  have hsplit : (fun i => σ (x i))
      = (fun i => evalPoly ((P i).coeffs (s.interval.inf i) (s.interval.sup i)) (x i))
        + fun i => σ (x i)
            - evalPoly ((P i).coeffs (s.interval.inf i) (s.interval.sup i)) (x i) := by
    funext i
    show σ (x i) = _ + _
    ring
  rw [hsplit]
  exact plus_outer _ _ (Set.add_mem_add hpmem (Interval.polyZonotope_contains _ hdev))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
