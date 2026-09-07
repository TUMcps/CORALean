import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyQ
import CORALean.NN.Layers.ActivationPoly

/-!
# The polynomial activation layer, read the other way

`enclose_outer` says the enclosed set contains the image; this says how much
larger it is. Every member is the polynomial at some point of the input set plus
something from the residual box, so it is within `2 · error` of that point's true
value — the fit's own error, and the box's, each once.

An inflation and not an inclusion in the image: `evalPoly` is exact and `plus` is
exact, but the box is a genuine widening, so the enclosed set really is bigger
and the honest statement is by how much. `Metric.closedBall` in the supremum norm
is what `Vec ℝ n` already carries, so no metric on sets is needed here or in
`Theorems.EncloseAtInflate`, which chains this along a network.

Two facts are derived rather than assumed: the input box is ordered, because a
polynomial zonotope is never empty, and the error is therefore nonnegative,
because `sound` bounds an absolute value at a point the box actually contains.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise ContSet

variable {σ : ℝ → ℝ} {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The enclosed set is inside the image inflated by `ε`, at any `ε` the
neurons' doubled errors fit under. -/
theorem Layer.activationPoly_subset_inflate (P : LayerRelaxation σ n m)
    (s : PolyZonotope (Vec ℝ n)) {ε : ℝ} (hε : 0 ≤ ε)
    (hP : ∀ i, 2 * (P i).error (s.interval.inf i) (s.interval.sup i) ≤ ε) :
    construct ((Layer.activationPoly P).enclose s)
      ⊆ (fun x i => σ (x i)) '' construct s + Metric.closedBall 0 ε := by -- --- PROOF ---
  -- the box is ordered, so `sound` at its left end says the error is nonnegative
  have herr : ∀ i, 0 ≤ (P i).error (s.interval.inf i) (s.interval.sup i) := fun i =>
    le_trans (abs_nonneg _)
      ((P i).sound (le_refl (s.interval.inf i)) (s.interval_inf_le_sup i))
  intro y hy
  have hy2 : y ∈ (s.dependent.evalPoly (P.coeffList s.interval)).construct
      + (Interval.polyZonotope (P.box s.interval)).construct := by
    rw [PolyZonotope.plus_exact]
    exact hy
  obtain ⟨u, hu, v, hv, rfl⟩ := hy2
  -- the polynomial part has no independent block, so it is a point of the factors
  obtain ⟨a, ha, hua⟩ := (s.dependent.evalPoly (P.coeffList s.interval)).exists_point_of_q_zero
    (PolyZonotope.evalPoly_q s.dependent (P.coeffList s.interval)) hu
  obtain ⟨a', ha'bound, ha'⟩ : ∃ a' : Fin s.dependent.p → ℝ, (∀ j, |a' j| ≤ 1) ∧
      (fun k => a' (Fin.cast (s.dependent.evalPoly_p (P.coeffList s.interval)) k)) = a :=
    ⟨fun j => a (Fin.cast (s.dependent.evalPoly_p (P.coeffList s.interval)).symm j),
      fun j => ha _, by funext k; simp⟩
  have hxs : s.dependent.point a' ∈ s.construct := by
    rw [PolyZonotope.dependent_exact s]
    exact s.dependent.point_mem_construct ha'bound
  have hxbox := PolyZonotope.interval_outer s hxs
  -- the polynomial the set evaluates to, one neuron's own fit per coordinate
  have hpval : (s.dependent.evalPoly (P.coeffList s.interval)).point
        (fun k => a' (Fin.cast (s.dependent.evalPoly_p (P.coeffList s.interval)) k))
      = fun i => evalPoly ((P i).coeffs (s.interval.inf i) (s.interval.sup i))
          (s.dependent.point a' i) := by
    rw [PolyZonotope.evalPoly_exact]
    funext i
    rw [LayerRelaxation.coeffList_coord, PolyZonotope.evalPolyReal_ofFn]
    rfl
  have hueq : u = fun i => evalPoly ((P i).coeffs (s.interval.inf i) (s.interval.sup i))
      (s.dependent.point a' i) := by
    rw [hua, ← hpval, ha']
  -- the residual box, centred at zero, reaches no further than half the budget
  have hbox : ∀ i, |(P.box s.interval).inf i| ≤ ε / 2 ∧ |(P.box s.interval).sup i| ≤ ε / 2 := by
    intro i
    constructor
    · show |-(P i).error (s.interval.inf i) (s.interval.sup i)| ≤ ε / 2
      rw [abs_neg, abs_of_nonneg (herr i)]
      linarith [hP i]
    · show |(P i).error (s.interval.inf i) (s.interval.sup i)| ≤ ε / 2
      rw [abs_of_nonneg (herr i)]
      linarith [hP i]
  have hvnorm : ‖v‖ ≤ ε / 2 :=
    Interval.polyZonotope_norm_le (by linarith) (fun i => (hbox i).1) (fun i => (hbox i).2) hv
  -- and each coordinate is within the fit's error plus the box's, which is `2 · error`
  have hres : ∀ i, |(u + v) i - σ (s.dependent.point a' i)| ≤ ε := by
    intro i
    have hvi : |v i| ≤ ε / 2 := by
      have h := norm_le_pi_norm v i
      rw [Real.norm_eq_abs] at h
      linarith
    have hsound : |σ (s.dependent.point a' i)
        - evalPoly ((P i).coeffs (s.interval.inf i) (s.interval.sup i)) (s.dependent.point a' i)|
        ≤ (P i).error (s.interval.inf i) (s.interval.sup i) := (P i).sound (hxbox i).1 (hxbox i).2
    obtain ⟨hd1, hd2⟩ := abs_le.mp hsound
    obtain ⟨hv1, hv2⟩ := abs_le.mp hvi
    show |u i + v i - σ (s.dependent.point a' i)| ≤ ε
    rw [congrFun hueq i, abs_le]
    constructor <;> linarith [hP i]
  -- that bound, read as a vector, is exactly what the ball holds
  have hball : (u + v) - (fun i => σ (s.dependent.point a' i))
      ∈ Metric.closedBall (0 : Vec ℝ n) ε := by
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hε]
    intro i
    rw [Real.norm_eq_abs]
    exact hres i
  have hmem := Set.add_mem_add
    (show (fun i => σ (s.dependent.point a' i))
      ∈ (fun x i => σ (x i)) '' construct s from ⟨s.dependent.point a', hxs, rfl⟩) hball
  have heq : (fun i => σ (s.dependent.point a' i))
      + ((u + v) - fun i => σ (s.dependent.point a' i)) = u + v := by abel
  rwa [heq] at hmem

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
