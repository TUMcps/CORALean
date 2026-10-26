module

public import CORALean.NN.Layers.Definitions.ActivationPoly
public import CORALean.NN.Layers.Definitions.Basic
public import CORALean.NN.Layers.Theorems.CoeffListCoord
public import CORALean.ContSet.PolyZonotope.Real.Theorems.DependentExact
public import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyExact
public import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyRealOfFn
public import CORALean.ContSet.PolyZonotope.Real.Theorems.ExistsPointOfQZero
public import CORALean.ContSet.PolyZonotope.Real.Theorems.PointMemConstruct
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Theorems.CapsuleIntervalContains
public import CORALean.ContSet.Conversion.Float.Theorems.Basic
public import CORALean.ContSet.Conversion.Float.Theorems.ConPolyZonoPolyZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalPolyZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.PolyZonotopeIntervalContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.CapsuleIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.ConPolyZonoIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.ConPolyZonoPolyZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ConZonotopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.Basic
public import CORALean.ContSet.Conversion.Real.Theorems.VPolytopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# What the exact polynomial activation layer encloses

ℝ-only, the representation being the exact polynomial zonotope: `σ` coordinatewise, where every
neuron's relaxation is sound. `dependent` is exact, so a point of the input is the point of the
dependent zonotope at some factors, and the fits' exact evaluation at those factors is the
polynomial there; the deviation from it is in the box.

## Inputs
* `P` – relaxation of every neuron

## Hypotheses
* `hP` – every neuron's relaxation is sound for the activation

## Conclusion
* the exact layer encloses the activation coordinatewise
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
private theorem aux_coord (P : LayerRelaxation ℝ n m) (J : Float.Interval (Vec ℝ n)) (i : Fin n) :
    ((P.coeffList J).map fun v => v i) = List.ofFn fun k => (P i).coeffs (J.inf i) (J.sup i) k :=
  LayerRelaxation.coeffList_coord P J i


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.activationPoly_encloses {P : LayerRelaxation ℝ n m}
    (hP : ∀ i, (P i).IsSound σ) : -- --- CONCL ---
    (Layer.activationPoly P).Encloses (fun x i => σ (x i)) := by -- --- PROOF ---
  refine ⟨fun s x hx => ?_⟩
  have hbox := PolyZonotope.interval_contains s hx
  have hxd : x ∈ s.dependent.construct := by
    rw [← PolyZonotope.dependent_exact s]
    exact hx
  obtain ⟨a, ha, hxa⟩ := s.dependent.exists_point_of_q_zero rfl hxd
  set J : Float.Interval (Vec ℝ n) := ⟨s.interval.inf, s.interval.sup⟩
  -- the polynomial part, one value per coordinate
  set pv : Vec ℝ n := fun i => evalPoly ((P i).coeffs (s.interval.inf i) (s.interval.sup i)) (x i)
  -- the polynomial part, read at the very factors `x` itself came from
  have hpval : (s.dependent.evalPoly (P.coeffList J)).point
        (fun k => a (Fin.cast (s.dependent.evalPoly_p (P.coeffList J)) k)) = pv := by
    rw [PolyZonotope.evalPoly_exact]
    funext i
    rw [aux_coord, PolyZonotope.evalPolyReal_ofFn, ← congrFun hxa i]
    rfl
  have hpmem : pv ∈ (s.dependent.evalPoly (P.coeffList J)).construct :=
    hpval ▸ PolyZonotope.point_mem_construct _ fun k => ha _
  -- and the deviation from that polynomial is inside the box, which is `sound`
  have hdev : (fun i => σ (x i) - pv i) ∈ (P.box J).nominal.construct := by
    intro i
    have hrel := abs_le.mp ((hP i).sound (hbox i).1 (hbox i).2)
    exact ⟨hrel.1, hrel.2⟩
  have hsplit : (fun i => σ (x i)) = pv + fun i => σ (x i) - pv i := by
    funext i
    show σ (x i) = _ + _
    ring
  rw [hsplit]
  exact plus_outer _ _ (Set.add_mem_add hpmem (Interval.polyZonotope_contains _ hdev))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
