module

public import CORALean.ContSet.Conversion.Float.Theorems.PolyZonotopeIntervalContains
public import CORALean.ContSet.PolyZonotope.Float.Theorems.CompactGensOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.EvalPowersOuter
public import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyRealOfFn
public import CORALean.NN.Layers.Definitions.Basic
public import CORALean.NN.Layers.Operations.ActivationPowers
public import CORALean.NN.Layers.Theorems.CoeffListCoord

@[expose] public section

/-!
# What the activation layer by the powers of the set encloses

`σ` coordinatewise, where every neuron's relaxation is sound for it: a point of the input has its
polynomials in `evalPowers` (and in `compactGens` of it), and the deviation of `σ` from them lies
in the box of the errors, which the independent generators added hold.

## Inputs
* `P` – relaxation of every neuron

## Hypotheses
* `hP` – every neuron's relaxation is sound for the activation

## Conclusion
* the layer encloses the activation coordinatewise
-/

-- Authors:       Claude Opus 5.5
-- Written:       16-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ} {σ : ℝ → ℝ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.activationPowers_encloses {P : LayerRelaxation 𝕋 n m}
    (hP : ∀ i, (P i).Encloses σ) : -- --- CONCL ---
    (Layer.activationPowers P).Encloses (fun x i => σ (x i)) := by -- --- PROOF ---
  refine ⟨fun s x hx => ?_⟩
  have hbox := PolyZonotope.interval_contains s hx
  -- the polynomials at the point, in the powers and in their compaction
  have hpmem := PolyZonotope.compactGens_outer _
    (PolyZonotope.evalPowers_outer s (P.coeffList s.interval) hx)
  set pv : Vec ℝ n := fun i =>
    Real.evalPoly (fun k => toReal ((P i).coeffs (s.interval.inf i) (s.interval.sup i) k)) (x i)
  have hpval : (fun i => Real.PolyZonotope.evalPolyReal
        ((P.coeffList s.interval).map fun v => toReal (v i)) (x i)) = pv := by
    funext i
    rw [LayerRelaxation.coeffList_coord, Real.PolyZonotope.evalPolyReal_ofFn]
    rfl
  -- the deviation from the polynomials is inside the box, which is `sound`
  have hdev : (fun i => σ (x i) - pv i) ∈ (P.box s.interval).toSet := by
    intro i
    have hrel := abs_le.mp ((hP i).sound (hbox i).1 (hbox i).2)
    refine ⟨?_, hrel.2⟩
    show toReal (neg ((P i).error (s.interval.inf i) (s.interval.sup i))) ≤ _
    rw [toReal_neg]
    exact hrel.1
  have hsplit : (fun i => σ (x i)) = pv + fun i => σ (x i) - pv i := by
    funext i
    show σ (x i) = _ + _
    ring
  rw [hsplit]
  exact Plus.plus_outer _ _ (Set.add_mem_add (hpval ▸ hpmem)
    (OfInterval.polyIndep.ofInterval_outer _ hdev))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
