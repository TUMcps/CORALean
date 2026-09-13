import CORALean.ContSet.Conversion.Real.Interval_to_PolyZonotope
import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Interval
import CORALean.ContSet.PolyZonotope.Real.Complexity.Dependent
import CORALean.ContSet.PolyZonotope.Real.Complexity.EvalPoly
import CORALean.ContSet.PolyZonotope.Real.Complexity.Plus
import CORALean.ContSet.PolyZonotope.Real.Instances
import CORALean.ContSet.PolyZonotope.Real.Theorems.DependentExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyQ
import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyRealOfFn
import CORALean.ContSet.PolyZonotope.Real.Theorems.ExistsPointOfQZero
import CORALean.ContSet.PolyZonotope.Real.Theorems.PointMemConstruct
import CORALean.NN.Layers.PolyRelaxation

/-!
# The activation layer at a polynomial relaxation

CORA's `evaluatePolyZonotopeNeuron` [1]: a fit per neuron, at the common
degree `PolyRelaxationPad` brings them to, evaluated through
`PolyZonotope.evalPoly` with only what the fits miss thrown into a box.
`Layer.activation` keeps a slope and boxes the rest; this keeps a degree-`m`
dependence, which is the precision refinement spends.

Pinned to `PolyZonotope`, not generic in `S`: no other representation is
closed under `evalPoly`, so a lone implementor is the honest answer for now.

The independent block is not ignored: `dependent` runs once on the input
first, and `exists_point_of_q_zero` carries its factors to every member.

[2, Alg. 1] is this at `m = 2`; the paper calls higher degree
`straightforward`. `evalPoly` is not [2, Prop. 2]'s own formula, though:
`dependent` makes every independent generator a fresh dependent one first,
so the cross terms Prop. 2 spends a new independent factor on are exact.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
* [2] N. Kochdumper et al. "Open- and Closed-Loop Neural Network Verification
      using Polynomial Zonotopes". arXiv:2207.02715, 2022.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   12-September-2026
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

/-- No independent generators survive `enclose`: `dependent` empties the input's
own before the fit runs, and the residual box lands in `Interval.polyZonotope`,
which is all dependent too. So `h` below is the *whole* generator count. -/
theorem Layer.activationPoly_enclose_q (P : LayerRelaxation σ n m) (s : PolyZonotope (Vec ℝ n)) :
    ((Layer.activationPoly P).enclose s).q = 0 := by
  show (PolyZonotope.plus (s.dependent.evalPoly (P.coeffList s.interval))
      (Interval.polyZonotope (P.box s.interval))).q = 0
  rw [PolyZonotope.plus_q, PolyZonotope.evalPoly_q, Interval.polyZonotope_q]

/-- [1, Lemma 4.3]: `enclose`'s generator count, a closed form in the input's own
`s.h + s.q` and the layer's shared degree `m` — `Alg. 1` line 9's padding — with
nothing of `P` beyond `m` reaching it, `n` more from the residual box. -/
theorem Layer.activationPoly_enclose_h (P : LayerRelaxation σ n m) (s : PolyZonotope (Vec ℝ n)) :
    ((Layer.activationPoly P).enclose s).h = (s.h + s.q + 1) *
      (∑ i ∈ Finset.range (m + 1), (s.h + s.q + 1) ^ i) + n := by -- --- PROOF ---
  show (PolyZonotope.plus (s.dependent.evalPoly (P.coeffList s.interval))
      (Interval.polyZonotope (P.box s.interval))).h = _
  have hlen : (P.coeffList s.interval).length = m + 1 := List.length_ofFn
  rw [PolyZonotope.plus_h, PolyZonotope.evalPoly_h, PolyZonotope.dependent_h, hlen,
    Interval.polyZonotope_h]

/-- [1, Lemma 4.3] in words: same order pattern `m` on the same input, same
generator count — whatever the individual neurons' own fits, `P` and `P'`
never appearing in `activationPoly_enclose_h`'s formula. -/
theorem Layer.activationPoly_enclose_h_indep (P P' : LayerRelaxation σ n m)
    (s : PolyZonotope (Vec ℝ n)) :
    ((Layer.activationPoly P).enclose s).h = ((Layer.activationPoly P').enclose s).h := by
  rw [Layer.activationPoly_enclose_h, Layer.activationPoly_enclose_h]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
