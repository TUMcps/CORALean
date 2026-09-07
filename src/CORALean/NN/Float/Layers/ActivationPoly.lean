import CORALean.ContSet.Conversion.Float.Interval_to_PolyZonotope
import CORALean.ContSet.Conversion.Float.PolyZonotope_to_Interval
import CORALean.ContSet.PolyZonotope.Float.Instances
import CORALean.ContSet.PolyZonotope.Float.Theorems.DependentNominal
import CORALean.ContSet.PolyZonotope.Float.Theorems.EvalPolyOuter
import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyRealOfFn
import CORALean.NN.Layers.ActivationPoly

/-!
# The activation layer at a polynomial relaxation, over a floating-point scalar

The exact layer's `PolyRelaxation` with `ℝ → ℝ → ℝ` replaced by `𝕋 → 𝕋 → 𝕋`, its
soundness against `σ` split into `PolyRelaxation.Sound` as `Activation` splits
`Relaxation`: nothing stored mentions `ℝ`, so the polynomial float layer is a
plain `def`. It is cheap for the same reason too — `Sound` is an inequality
against `error`, so a fit computed in floating point is sound as it stands and
which polynomial was fitted is still free.

The layer itself rounds nowhere. `LayerRelaxation.box` is centred at zero, where
`neg` is exact, and the polynomial's own rounding is `evalPoly`'s, every Horner
step charging its product and its centre shift to the representation's error
box. `dependent` does more work here than over ℝ: it frees that box as well as
the independent generators, so what `evalPoly` evaluates carries every
coefficient the input had, rounding included.

A relaxation per neuron, all at one degree, as over ℝ: an order pattern
[1, Eq. 23] gives the neurons different orders and padding makes them agree.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   07-September-2026
-- Last revision: 07-September-2026


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise ContSet Plus FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {σ : ℝ → ℝ} {m n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- A degree-`m` fit per box, in floats and nothing else. -/
structure PolyRelaxation (𝕋 : Type) [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] (m : ℕ) where
  coeffs : 𝕋 → 𝕋 → Fin (m + 1) → 𝕋
  error : 𝕋 → 𝕋 → 𝕋

/-- That it encloses `σ` on every box the stored floats describe. The bounds and
coefficients arrive in `𝕋` and the argument stays real: what the layer encloses
is the exact function [1]. -/
structure PolyRelaxation.Sound (P : PolyRelaxation 𝕋 m) (σ : ℝ → ℝ) : Prop where
  sound {l u : 𝕋} {t : ℝ} (hl : toReal l ≤ t) (hu : t ≤ toReal u) :
    |σ t - Real.evalPoly (fun k => toReal (P.coeffs l u k)) t| ≤ toReal (P.error l u)

/-- A layer's abstraction: one relaxation per neuron, all at one degree. -/
abbrev LayerRelaxation (𝕋 : Type) [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] (n m : ℕ) :=
  Fin n → PolyRelaxation 𝕋 m

/-- Neuron `i`'s coefficient of `t ^ k`, from its own fit on its own range. -/
def LayerRelaxation.coeffVec (P : LayerRelaxation 𝕋 n m) (I : Interval 𝕋 n)
    (k : Fin (m + 1)) : Vec 𝕋 n := fun i => (P i).coeffs (I.inf i) (I.sup i) k

/-- Those vectors as `PolyZonotope.evalPoly` takes them, lowest degree first. -/
def LayerRelaxation.coeffList (P : LayerRelaxation 𝕋 n m) (I : Interval 𝕋 n) :
    List (Vec 𝕋 n) := List.ofFn (P.coeffVec I)

/-- Coordinate `i` of the list, read as reals, is neuron `i`'s own coefficients:
what `evalPoly_outer` states its exact side against. -/
theorem LayerRelaxation.coeffList_coord (P : LayerRelaxation 𝕋 n m) (I : Interval 𝕋 n)
    (i : Fin n) : ((P.coeffList I).map fun v => toReal (v i))
      = List.ofFn fun k => toReal ((P i).coeffs (I.inf i) (I.sup i) k) := by
  rw [LayerRelaxation.coeffList, List.map_ofFn]
  rfl

/-- The box each neuron's deviation from its own polynomial is confined to.
Centred at zero, where `neg` is exact, so this box rounds nowhere. -/
def LayerRelaxation.box (P : LayerRelaxation 𝕋 n m) (I : Interval 𝕋 n) : Interval 𝕋 n where
  inf := fun i => neg ((P i).error (I.inf i) (I.sup i))
  sup := fun i => (P i).error (I.inf i) (I.sup i)

/-- The activation layer of a polynomial relaxation: `dependent` first, then
each neuron's fit on the set, then the residual box. -/
def Layer.activationPoly (P : LayerRelaxation 𝕋 n m) :
    Real.Layer (PolyZonotope 𝕋) n n where
  enclose s := plus (s.dependent.evalPoly (P.coeffList s.interval))
    (Interval.polyZonotope (P.box s.interval))

/-- `σ` coordinatewise is what the layer encloses, which is where `σ` first
appears: `Layer.activationPoly` itself never sees it. -/
theorem Layer.activationPoly_sound {P : LayerRelaxation 𝕋 n m}
    (hP : ∀ i, (P i).Sound σ) :
    (Layer.activationPoly P).Sound (fun x i => σ (x i)) := by -- --- PROOF ---
  refine ⟨fun s x hx => ?_⟩
  have hbox := PolyZonotope.interval_contains s hx
  -- `dependent` leaves no independent generator, so `x` is a nominal point
  obtain ⟨a, ha, hxa⟩ := (nominal s.dependent).exists_point_of_q_zero rfl
    (PolyZonotope.dependent_nominal s hx)
  have hpt : Real.PolyZonotope.point (nominal s.dependent) a = x := hxa.symm
  have hpmem := PolyZonotope.evalPoly_outer s.dependent (P.coeffList s.interval)
    ⟨a, ha, rfl⟩
  -- the polynomial part, one neuron's own fit per coordinate
  have hpval : (fun i => Real.PolyZonotope.evalPolyReal
        ((P.coeffList s.interval).map fun v => toReal (v i))
        (Real.PolyZonotope.point (nominal s.dependent) a i))
      = fun i => Real.evalPoly
          (fun k => toReal ((P i).coeffs (s.interval.inf i) (s.interval.sup i) k)) (x i) := by
    funext i
    rw [LayerRelaxation.coeffList_coord, Real.PolyZonotope.evalPolyReal_ofFn, congrFun hpt i]
    rfl
  -- and the deviation from that polynomial is inside the box, which is `sound`
  have hdev : (fun i => σ (x i) - Real.evalPoly
        (fun k => toReal ((P i).coeffs (s.interval.inf i) (s.interval.sup i) k)) (x i))
      ∈ (P.box s.interval).construct := by
    intro i
    have hrel := abs_le.mp ((hP i).sound (hbox i).1 (hbox i).2)
    refine ⟨?_, hrel.2⟩
    show toReal (neg ((P i).error (s.interval.inf i) (s.interval.sup i))) ≤ _
    rw [toReal_neg]
    exact hrel.1
  -- the value is that polynomial plus that deviation, which is what `plus` holds
  have hsplit : (fun i => σ (x i))
      = (fun i => Real.evalPoly
            (fun k => toReal ((P i).coeffs (s.interval.inf i) (s.interval.sup i) k)) (x i))
        + fun i => σ (x i) - Real.evalPoly
            (fun k => toReal ((P i).coeffs (s.interval.inf i) (s.interval.sup i) k)) (x i) := by
    funext i
    show σ (x i) = _ + _
    ring
  rw [hsplit]
  exact plus_outer _ _ (Set.add_mem_add (hpval ▸ hpmem)
    (Interval.polyZonotope_contains _ hdev))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
