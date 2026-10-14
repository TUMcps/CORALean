module

public import CORALean.ContSet.PolyZonotope.Float.Theorems.DependentNominal
public import CORALean.ContSet.PolyZonotope.Float.Theorems.EvalPolyOuter
public import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyRealOfFn
public import CORALean.ContSet.PolyZonotope.Real.Theorems.ExistsPointOfQZero
public import CORALean.NN.Layers.Operations.ActivationPoly
public import CORALean.NN.Layers.Theorems.CoeffListCoord

@[expose] public section

/-!
# What the polynomial activation layer encloses

`σ` coordinatewise, where every neuron's relaxation is sound for it — which is where `σ` first
appears: `dependent` leaves no independent generator, so a point of the input is a nominal point
at some factors, the fits' outward evaluation holds the polynomial there, and the box the
deviation from it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ} {σ : ℝ → ℝ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.activationPoly_sound {P : LayerRelaxation 𝕋 n m}
    (hP : ∀ i, (P i).Sound σ) :
    (Layer.activationPoly P).Sound (fun x i => σ (x i)) := by -- --- PROOF ---
  refine ⟨fun s x hx => ?_⟩
  have hbox := PolyZonotope.interval_contains s hx
  -- `dependent` leaves no independent generator, so `x` is a nominal point
  obtain ⟨a, ha, hxa⟩ := (InflatedContSet.nominal s.dependent).exists_point_of_q_zero rfl
    (PolyZonotope.dependent_nominal s hx)
  have hpt : Real.PolyZonotope.point (InflatedContSet.nominal s.dependent) a = x := hxa.symm
  have hpmem := PolyZonotope.evalPoly_outer s.dependent (P.coeffList s.interval)
    ⟨a, ha, rfl⟩
  -- the polynomial part, one value per coordinate
  set pv : Vec ℝ n := fun i =>
    Real.evalPoly (fun k => toReal ((P i).coeffs (s.interval.inf i) (s.interval.sup i) k)) (x i)
  -- each neuron's own fit, evaluated at the box's point
  have hpval : (fun i => Real.PolyZonotope.evalPolyReal
        ((P.coeffList s.interval).map fun v => toReal (v i))
        (Real.PolyZonotope.point (InflatedContSet.nominal s.dependent) a i))
      = pv := by
    funext i
    rw [LayerRelaxation.coeffList_coord, Real.PolyZonotope.evalPolyReal_ofFn, congrFun hpt i]
    rfl
  -- and the deviation from that polynomial is inside the box, which is `sound`
  have hdev : (fun i => σ (x i) - pv i)
      ∈ (P.box s.interval).construct := by
    intro i
    have hrel := abs_le.mp ((hP i).sound (hbox i).1 (hbox i).2)
    refine ⟨?_, hrel.2⟩
    show toReal (neg ((P i).error (s.interval.inf i) (s.interval.sup i))) ≤ _
    rw [toReal_neg]
    exact hrel.1
  -- the value is that polynomial plus that deviation, which is what `plus` holds
  have hsplit : (fun i => σ (x i)) = pv + fun i => σ (x i) - pv i := by
    funext i
    show σ (x i) = _ + _
    ring
  rw [hsplit]
  exact Plus.plus_outer _ _ (Set.add_mem_add (hpval ▸ hpmem)
    (Interval.polyZonotope_contains _ hdev))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
