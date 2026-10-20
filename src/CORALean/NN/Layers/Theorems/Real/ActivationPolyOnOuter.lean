module

public import CORALean.NN.Layers.Definitions.ActivationPoly
public import CORALean.NN.Layers.Theorems.CoeffListCoord
public import CORALean.ContSet.PolyZonotope.Real.Theorems.DependentExact
public import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyExact
public import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyRealOfFn
public import CORALean.ContSet.PolyZonotope.Real.Theorems.ExistsPointOfQZero
public import CORALean.ContSet.PolyZonotope.Real.Theorems.PointMemConstruct
public import CORALean.ContSet.Conversion.Float.Theorems.ConPolyZonoPolyZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalPolyZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ConPolyZonoPolyZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.Basic

@[expose] public section

/-!
# The exact polynomial activation layer at a box handed to it

ℝ-only, as the layer is. What survives is pointwise soundness, not `Layer.Encloses`: `J` answers
for the points it contains and no others, so the claim is at a point of the input that `J` holds
too — what [1, Prop. 4.2]'s loop has, the enclosure sound for the exact set even where it says
nothing about the set this iteration computed.

## Inputs
* `P` – relaxation of every neuron
* `J` – box handed to the fits
* `s` – input polynomial zonotope
* `x` – point of the input set

## Hypotheses
* `hP` – every neuron's relaxation is sound for the activation
* `hx` – point lies in the input set
* `hJ` – point lies in the handed box

## Conclusion
* the activation of the point lies in the layer's output set

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise ContSet Plus

variable {σ : ℝ → ℝ} {m n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- the polynomial part, one neuron's own fit per coordinate, read without the scalar
theorem aux_coord (P : LayerRelaxation ℝ n m) (J : Float.Interval (Vec ℝ n)) (i : Fin n) :
    ((P.coeffList J).map fun v => v i) = List.ofFn fun k => (P i).coeffs (J.inf i) (J.sup i) k :=
  LayerRelaxation.coeffList_coord P J i


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.activationPolyOn_outer {P : LayerRelaxation ℝ n m} (hP : ∀ i, (P i).Sound σ)
    (J : Interval (Vec ℝ n)) (s : 𝒫𝒵 n) {x : Vec ℝ n} (hx : x ∈ construct s)
    (hJ : x ∈ J.construct) : -- --- CONCL ---
    (fun i => σ (x i)) ∈ construct ((Layer.activationPolyOn P J).enclose s) := by -- --- PROOF ---
  have hxd : x ∈ s.dependent.construct := by
    rw [← PolyZonotope.dependent_exact s]
    exact hx
  obtain ⟨a, ha, hxa⟩ := s.dependent.exists_point_of_q_zero rfl hxd
  set J' : Float.Interval (Vec ℝ n) := ⟨J.inf, J.sup⟩
  -- the polynomial part, read at the very factors `x` itself came from
  have hpval : (s.dependent.evalPoly (P.coeffList J')).point
        (fun k => a (Fin.cast (s.dependent.evalPoly_p (P.coeffList J')) k))
      = fun i => evalPoly ((P i).coeffs (J.inf i) (J.sup i)) (x i) := by
    rw [PolyZonotope.evalPoly_exact]
    funext i
    rw [aux_coord, PolyZonotope.evalPolyReal_ofFn, ← congrFun hxa i]
    rfl
  have hpmem : (fun i => evalPoly ((P i).coeffs (J.inf i) (J.sup i)) (x i))
      ∈ (s.dependent.evalPoly (P.coeffList J')).construct :=
    hpval ▸ PolyZonotope.point_mem_construct _ fun k => ha _
  -- `J` is asked for nothing but the two ends the fit was made between
  have hdev : (fun i => σ (x i) - evalPoly ((P i).coeffs (J.inf i) (J.sup i)) (x i))
      ∈ (P.box J').nominal.construct := by
    intro i
    have hrel := abs_le.mp ((hP i).sound (hJ i).1 (hJ i).2)
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
