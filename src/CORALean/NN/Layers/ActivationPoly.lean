import CORALean.ContSet.Conversion.Real.Interval_to_PolyZonotope
import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Interval
import CORALean.ContSet.PolyZonotope.Real.Instances
import CORALean.ContSet.PolyZonotope.Real.Theorems.DependentExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.ExistsPointOfQZero
import CORALean.ContSet.PolyZonotope.Real.Theorems.PointMemConstruct
import CORALean.NN.Layers.PolyRelaxation

/-!
# The activation layer at a polynomial relaxation

CORA's `evaluatePolyZonotopeNeuron` [1]: each neuron's own degree-`m` fit,
evaluated on the set through `PolyZonotope.evalPoly`, with only what the fit
misses thrown into a box. `Layer.activation` keeps a slope and boxes the rest;
this keeps a degree-`m` dependence on the input factors, and that difference is
the precision a refinement loop has to spend.

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
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Pointwise ContSet Plus

variable {σ : ℝ → ℝ} {m n : ℕ}

/-- Horner over a list of coefficients is the monomial sum they stand for, which
is how `evalPolyReal` meets `evalPoly`. -/
theorem PolyZonotope.evalPolyReal_ofFn (t : ℝ) : ∀ {k : ℕ} (c : Fin k → ℝ),
    PolyZonotope.evalPolyReal (List.ofFn c) t = ∑ j, c j * t ^ (j : ℕ) := by
  intro k
  induction k with
  | zero => intro c; simp [PolyZonotope.evalPolyReal]
  | succ k ih =>
    intro c
    rw [List.ofFn_succ, PolyZonotope.evalPolyReal, ih, Fin.sum_univ_succ, Finset.mul_sum]
    -- the `t` Horner factors out is the extra degree each remaining term carries
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    exact congrArg _ (Finset.sum_congr rfl fun j _ => by ring)

/-- Neuron `i`'s coefficient of `t ^ k`, taken on its own input range: one
vector per degree, which is how `evalPoly` reads a coefficient. -/
def PolyRelaxation.coeffVec (P : PolyRelaxation σ m) (I : Interval (Vec ℝ n))
    (k : Fin (m + 1)) : Vec ℝ n := fun i => P.coeffs (I.inf i) (I.sup i) k

/-- Those vectors as `PolyZonotope.evalPoly` takes them, lowest degree first. -/
def PolyRelaxation.coeffList (P : PolyRelaxation σ m) (I : Interval (Vec ℝ n)) :
    List (Vec ℝ n) := List.ofFn (P.coeffVec I)

/-- Coordinate `i` of the list is neuron `i`'s own coefficients, which is what
makes one `evalPoly` call carry `n` different polynomials. -/
theorem PolyRelaxation.coeffList_coord (P : PolyRelaxation σ m) (I : Interval (Vec ℝ n))
    (i : Fin n) : ((P.coeffList I).map fun v => v i)
      = List.ofFn (P.coeffs (I.inf i) (I.sup i)) := by
  rw [PolyRelaxation.coeffList, List.map_ofFn]
  rfl

/-- The box each neuron's deviation from its own polynomial is confined to.
Centred at zero, `sound` bounding an absolute value and nothing else. -/
def PolyRelaxation.box (P : PolyRelaxation σ m) (I : Interval (Vec ℝ n)) :
    Interval (Vec ℝ n) where
  inf := fun i => -P.error (I.inf i) (I.sup i)
  sup := fun i => P.error (I.inf i) (I.sup i)

/-- The activation layer of a polynomial relaxation: `dependent` first, then
each neuron's fit on the set, then the residual box. -/
noncomputable def Layer.activationPoly (P : PolyRelaxation σ m) : Layer 𝒫𝒵 n n where
  eval x := fun i => σ (x i)
  propagate s := plus (s.dependent.evalPoly (P.coeffList s.interval))
    (Interval.polyZonotope (P.box s.interval))
  propagate_outer s x hx := by
    have hbox := PolyZonotope.interval_outer s hx
    have hxd : x ∈ s.dependent.construct := by
      rw [← PolyZonotope.dependent_exact s]
      exact hx
    obtain ⟨a, ha, hxa⟩ := s.dependent.exists_point_of_q_zero rfl hxd
    -- the polynomial part, read at the very factors `x` itself came from
    have hpval : (s.dependent.evalPoly (P.coeffList s.interval)).point
          (fun k => a (Fin.cast (s.dependent.evalPoly_p (P.coeffList s.interval)) k))
        = fun i => evalPoly (P.coeffs (s.interval.inf i) (s.interval.sup i)) (x i) := by
      rw [PolyZonotope.evalPoly_exact]
      funext i
      rw [PolyRelaxation.coeffList_coord, PolyZonotope.evalPolyReal_ofFn, ← congrFun hxa i]
      rfl
    have hpmem : (fun i => evalPoly (P.coeffs (s.interval.inf i) (s.interval.sup i)) (x i))
        ∈ (s.dependent.evalPoly (P.coeffList s.interval)).construct :=
      hpval ▸ PolyZonotope.point_mem_construct _ fun k => ha _
    -- and the deviation from that polynomial is inside the box, which is `sound`
    have hdev : (fun i => σ (x i)
          - evalPoly (P.coeffs (s.interval.inf i) (s.interval.sup i)) (x i))
        ∈ (P.box s.interval).construct := by
      intro i
      have hrel := abs_le.mp (P.sound (hbox i).1 (hbox i).2)
      exact ⟨hrel.1, hrel.2⟩
    have hsplit : (fun i => σ (x i))
        = (fun i => evalPoly (P.coeffs (s.interval.inf i) (s.interval.sup i)) (x i))
          + fun i => σ (x i)
              - evalPoly (P.coeffs (s.interval.inf i) (s.interval.sup i)) (x i) := by
      funext i
      show σ (x i) = _ + _
      ring
    rw [hsplit]
    exact plus_outer _ _ (Set.add_mem_add hpmem (Interval.subset_polyZonotope _ hdev))

end CORALean.Real
