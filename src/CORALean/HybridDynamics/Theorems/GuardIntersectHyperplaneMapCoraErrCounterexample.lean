module

public import CORALean.HybridDynamics.Operations.GuardIntersectHyperplaneMapCoraErr
public import CORALean.HybridDynamics.Theorems.AbstractionErrorCoraEqZero
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpTaylor
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMem
public import CORALean.ContSet.Zonotope.Real.Operations.QuadMap
public import CORALean.ContSet.Zonotope.Real.Operations.UnitIntervalMul
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# With CORA's printed error, the hyperplane map misses a guard hit

`Location.guardIntersectHyperplaneMapCoraErr`, the guard mapping with `err1` overwritten as in
CORA's `aux_abstractionError`, against a run that hits the hyperplane. The location `ẋ = Ax`,
`A` the shift of `ℝ³` (`A³ = 0`), no inputs, from `R₀ = {(0, 0, 1)}` onto `x₂ = 2` (`n = e₂`,
`d = 2`), `tmax = 2`, `η = 3`, any reduction orders: the run `x(t) = (t²/2, t, 1)` is on the
hyperplane at `t = 2`, at `(2, 2, 1)`. CORA's error set is `{0}`
(`GuardMap.abstractionErrorCora_eq_zero`), the start set a point, so the result is the one point
`k = x₀ + (Ax₀ + b)(d − nᵀx₀)/Λ = (1, 2, 1)` of the constant flow `b = (½, 0, 0)`.
`Location.guardIntersectHyperplaneMap_outer`, with every `err1` summand, holds the hit.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The shift of `ℝ³`. -/
def aux_hpMapCoraCex_A : Mat ℝ 3 3 := !![0, 1, 0; 0, 0, 1; 0, 0, 0]

theorem aux_hpMapCoraCex_sq : aux_hpMapCoraCex_A ^ 2 = !![0, 0, 1; 0, 0, 0; 0, 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sq, Matrix.mul_apply, Fin.sum_univ_three, aux_hpMapCoraCex_A]

theorem aux_hpMapCoraCex_cube : aux_hpMapCoraCex_A ^ 3 = 0 := by
  rw [pow_succ, aux_hpMapCoraCex_sq]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, aux_hpMapCoraCex_A]

/-- `W = e^{2|A|} − T₃(2|A|) = 0`: `|A| = A` and `(2A)³ = 0`. -/
theorem aux_hpMapCoraCex_W :
    MatExp.expRemainderMat aux_hpMapCoraCex_A 2 3 = 0 := by -- --- PROOF ---
  have habs : MatExp.absMat aux_hpMapCoraCex_A = aux_hpMapCoraCex_A := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [MatExp.absMat, aux_hpMapCoraCex_A]
  rw [MatExp.expRemainderMat, habs, exp_eq_tsum ℝ, MatExp.expTaylor]
  dsimp only
  rw [tsum_eq_sum (s := Finset.range (3 + 1)) fun k hk => ?_, sub_self]
  have hk' : 3 ≤ k := by simp at hk; omega
  rw [show k = 3 + (k - 3) by omega, pow_add, smul_pow, aux_hpMapCoraCex_cube, smul_zero,
    zero_mul, smul_zero]

/-- `b = Θ(1)x₀ = ½A²x₀`. -/
theorem aux_hpMapCoraCex_b :
    GuardMap.sdcInput aux_hpMapCoraCex_A 0 1 3 ![0, 0, 1] = ![1 / 2, 0, 0] := by
  simp only [GuardMap.sdcInput, Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ,
    Finset.sum_range_zero, Nat.reduceAdd, aux_hpMapCoraCex_sq, aux_hpMapCoraCex_cube,
    smul_zero, add_zero, zero_add, mulVec_zero]
  ext i; fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three, Nat.factorial]

theorem aux_hpMapCoraCex_reduceGirard_ofPoint (v : Vec ℝ n) (o : ℕ) :
    (Zonotope.ofPoint v).reduceGirard o = Zonotope.ofPoint v := by
  unfold Zonotope.reduceGirard
  rw [dif_neg (by simp [Zonotope.ofPoint])]

theorem aux_hpMapCoraCex_reduceGirard_c (Z : Zonotope (Vec ℝ n)) (o : ℕ) :
    (Z.reduceGirard o).c = Z.c := by
  unfold Zonotope.reduceGirard
  split_ifs <;> rfl

theorem aux_hpMapCoraCex_reduceGirard {Z : Zonotope (Vec ℝ n)} (h : ∀ j, Z.G j = 0)
    (o : ℕ) : ∀ j, (Z.reduceGirard o).G j = 0 := by -- --- PROOF ---
  by_cases hlt : o * n < Z.h
  · rw [show Z.reduceGirard o = Z.reduceBy (Z.girardSplit o hlt) from dif_pos hlt]
    intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp [Zonotope.reduceBy, h]
    · ext i; simp [Zonotope.reduceBy, h]
  · rw [show Z.reduceGirard o = Z from dif_neg hlt]
    exact h

theorem aux_hpMapCoraCex_ofPoint (v : Vec ℝ n) : ∀ j, (Zonotope.ofPoint v).G j = 0 :=
  fun j => j.elim0

theorem aux_hpMapCoraCex_plus {Z₁ Z₂ : Zonotope (Vec ℝ n)} (h₁ : ∀ j, Z₁.G j = 0)
    (h₂ : ∀ j, Z₂.G j = 0) : ∀ j, (Z₁.plus Z₂).G j = 0 := fun j => by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp [Zonotope.plus, h₁, h₂]

theorem aux_hpMapCoraCex_mtimes (M : Mat ℝ n n) {Z : Zonotope (Vec ℝ n)}
    (h : ∀ j, Z.G j = 0) : ∀ j, (Zonotope.mtimes M Z).G j = 0 := fun j => by
  simp [Zonotope.mtimes, h]

/-- An interval matrix applied to `{0}`, or `[0, 0]` applied to a point. -/
theorem aux_hpMapCoraCex_mtimesIM (IM : Interval (Mat ℝ n n)) {Z : Zonotope (Vec ℝ n)}
    (h : ∀ j, Z.G j = 0) (h0 : ∀ i j, IM.radius i j * |Z.c j| = 0) :
    ∀ j, (Zonotope.mtimesIntervalMat IM Z).G j = 0 := by -- --- PROOF ---
  intro j
  have hr : ∀ i, Zonotope.radiusReach IM Z i = 0 := fun i => by
    simp only [Zonotope.radiusReach, Zonotope.absBound, h, Pi.zero_apply, abs_zero,
      Finset.sum_const_zero, add_zero, h0]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp [Zonotope.mtimesIntervalMat, h]
  · ext i; simp [Zonotope.mtimesIntervalMat, hr]

theorem aux_hpMapCoraCex_append_zero {a b m : ℕ} (x : Fin (a + b)) :
    Fin.append (fun (_ : Fin a) (_ : Fin m) => (0 : ℝ)) (fun (_ : Fin b) (_ : Fin m) => (0 : ℝ))
      x = fun _ => 0 := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) x <;> simp

/-- `quadMap` of `{0}` is `{0}`. -/
theorem aux_hpMapCoraCex_quadMap {m : ℕ} (D : Fin m → Mat ℝ n n) {Z : Zonotope (Vec ℝ n)}
    (hc : Z.c = 0) (h : ∀ j, Z.G j = 0) :
    (Z.quadMap D).c = 0 ∧ ∀ j, (Z.quadMap D).G j = 0 := by
  refine ⟨by ext i; simp [Zonotope.quadMap, hc, h], fun j => ?_⟩
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · ext i; simp [Zonotope.quadMap, hc, h, aux_hpMapCoraCex_append_zero]
  · ext i; simp [Zonotope.quadMap, h]

theorem aux_hpMapCoraCex_unitIntervalMul {Z : Zonotope (Vec ℝ n)} (hc : Z.c = 0)
    (h : ∀ j, Z.G j = 0) : ∀ j, Z.unitIntervalMul.G j = 0 := fun j => by
  refine Fin.cases ?_ (fun j => ?_) j <;> simp [Zonotope.unitIntervalMul, hc, h]

/-- `R_quad` of `{0}` is `{0}`. -/
theorem aux_hpMapCoraCex_quadMapMatZono {m ν : ℕ} (D : Fin m → Mat ℝ n n)
    (K : Fin ν → Fin m → Mat ℝ n n) {Z : Zonotope (Vec ℝ n)} (hc : Z.c = 0)
    (h : ∀ j, Z.G j = 0) :
    (Zonotope.quadMapMatZono D K Z).c = 0 ∧
      ∀ j, (Zonotope.quadMapMatZono D K Z).G j = 0 := by -- --- PROOF ---
  refine ⟨(aux_hpMapCoraCex_quadMap D hc h).1, fun j => ?_⟩
  refine Fin.addCases (fun j => ?_) (fun l => ?_) j
  · simp only [Zonotope.quadMapMatZono, Fin.append_left]
    exact (aux_hpMapCoraCex_quadMap D hc h).2 j
  · simp only [Zonotope.quadMapMatZono, Fin.append_right]
    exact aux_hpMapCoraCex_unitIntervalMul (aux_hpMapCoraCex_quadMap _ hc h).1
      (aux_hpMapCoraCex_quadMap _ hc h).2 _

/-- A point of a zonotope whose generators are `0` is its centre. -/
theorem aux_hpMapCoraCex_mem {Z : Zonotope (Vec ℝ n)} (h : ∀ j, Z.G j = 0)
    {x : Vec ℝ n} (hx : x ∈ Z.construct) : x = Z.c := by
  obtain ⟨β, -, rfl⟩ := hx
  simp [h]


/-- The projection onto `cᵀx = d` of a zonotope whose generators are `0` is a point. -/
theorem aux_hpMapCoraCex_proj {R : Zonotope (Vec ℝ n)} (h : ∀ j, R.G j = 0) (c : Vec ℝ n)
    (d : ℝ) {x : Vec ℝ n} (hx : x ∈ (ContSet.projectOnHyperplane (S := 𝒵) R c d).construct) :
    x = (1 - vecMulVec c c) *ᵥ R.c + d • c := by -- --- PROOF ---
  change x ∈ ((Zonotope.mtimes (1 - vecMulVec c c) R).plus (Zonotope.ofPoint (d • c))).construct
    at hx
  have := aux_hpMapCoraCex_mem (aux_hpMapCoraCex_plus (aux_hpMapCoraCex_mtimes _ h)
    (aux_hpMapCoraCex_ofPoint _)) hx
  simpa [Zonotope.plus, Zonotope.mtimes, Zonotope.ofPoint] using this


-- =======================================  MAIN THEOREM  ======================================= --

/-- A run of a linear location from `R₀` hits `nᵀx = d` at `t ≤ tmax` outside the set
`Location.guardIntersectHyperplaneMapCoraErr` returns, `η = 3`, for all reduction orders. -/
theorem Location.guardIntersectHyperplaneMapCoraErr_counterexample :
    ∃ (ℓ : Location 𝒵 𝒵 Unit ℝ 3) (nv : Vec ℝ 3) (d : ℝ) (R₀ : Zonotope (Vec ℝ 3))
      (tmax τ t : ℝ) (x u : ℝ → Vec ℝ 3), ℓ.Trajectory τ x u ∧ x 0 ∈ R₀.construct ∧
      t ∈ Set.Icc 0 τ ∧ t ≤ tmax ∧ nv ⬝ᵥ x t = d ∧
      ∀ guardOrder zonotopeOrder : ℕ, ∃ Z,
        ℓ.guardIntersectHyperplaneMapCoraErr nv d R₀ tmax 3 guardOrder zonotopeOrder = some Z ∧
        x t ∉ Z.construct := by -- --- PROOF ---
  set x : ℝ → Vec ℝ 3 := fun t => ![t ^ 2 / 2, t, 1] with hx
  set inv : Zonotope (Vec ℝ 3) := ⟨2, ![1, 1, 1], ![![1, 0, 0], ![0, 1, 0]]⟩
  refine ⟨⟨inv, ⟨aux_hpMapCoraCex_A⟩, Zonotope.ofPoint 0, []⟩, ![0, 1, 0], 2,
    Zonotope.ofPoint ![0, 0, 1], 2, 2, 2, x, fun _ => 0, ⟨by norm_num, ?_, ?_, ?_⟩, ?_,
    ⟨by norm_num, le_rfl⟩, le_rfl, ?_, ?_⟩
  -- the run: `ẋ = Ax`, inside the box `inv`
  · intro t _; exact Zonotope.mem_ofPoint (0 : Vec ℝ 3)
  · intro t _
    refine hasDerivWithinAt_pi.2 fun i => ?_
    fin_cases i
    · exact ((HasDerivAt.div_const (hasDerivAt_pow 2 t) 2).hasDerivWithinAt).congr_deriv
        (by simp [x, aux_hpMapCoraCex_A])
    · exact ((hasDerivAt_id t).hasDerivWithinAt).congr_deriv
        (by simp [x, aux_hpMapCoraCex_A])
    · exact ((hasDerivAt_const t (1 : ℝ)).hasDerivWithinAt).congr_deriv
        (by simp [x, aux_hpMapCoraCex_A])
  · rintro t ⟨h0, h2⟩
    refine ⟨![t ^ 2 / 2 - 1, t - 1], fun j => ?_, ?_⟩
    · fin_cases j <;> simp <;> rw [abs_le] <;> constructor <;> nlinarith
    · ext i; fin_cases i <;> simp [x, inv, Fin.sum_univ_two]
  · simpa [x] using Zonotope.mem_ofPoint (![0, 0, 1] : Vec ℝ 3)
  · simp [x, dotProduct, Fin.sum_univ_three]
  -- CORA's map: the error is `{0}` (`A³ = 0`, `W = 0`), and the start set is not reduced
  intro go zo
  obtain ⟨hc, hG⟩ := GuardMap.abstractionErrorCora_eq_zero aux_hpMapCoraCex_A ![0, 0, 1]
    (2 / 2) 2 aux_hpMapCoraCex_cube aux_hpMapCoraCex_W
  dsimp only [Location.guardIntersectHyperplaneMapCoraErr]
  rw [aux_hpMapCoraCex_reduceGirard_ofPoint]
  -- `Λ = nᵀ(Ax₀ + b) = 1` on the point `R₀`
  have hΛ : Zonotope.halfspaceRange ![0, 1, 0] 0
      ((Zonotope.mtimes aux_hpMapCoraCex_A (Zonotope.ofPoint ![0, 0, 1])).plus
        (Zonotope.ofPoint (GuardMap.sdcInput aux_hpMapCoraCex_A (Zonotope.ofPoint 0).c (2 / 2) 3
          (Zonotope.ofPoint ![0, 0, 1]).c))) = (1, 1) := by
    simp only [Zonotope.ofPoint, show (2 : ℝ) / 2 = 1 by norm_num]
    rw [aux_hpMapCoraCex_b]
    simp [Zonotope.halfspaceRange, Zonotope.plus, Zonotope.mtimes, dotProduct,
      Fin.sum_univ_three, aux_hpMapCoraCex_A, Matrix.vecHead, Matrix.vecTail]
  rw [hΛ, if_pos (by norm_num)]
  -- every generator of the result is `0`: a member is its centre, the projected `k`
  refine ⟨_, rfl, fun hmem => ?_⟩
  have heq := congrFun (aux_hpMapCoraCex_proj (aux_hpMapCoraCex_reduceGirard
    (aux_hpMapCoraCex_plus (aux_hpMapCoraCex_plus (aux_hpMapCoraCex_plus
      (aux_hpMapCoraCex_ofPoint _) (aux_hpMapCoraCex_mtimes _ fun j => j.elim0))
      (aux_hpMapCoraCex_mtimesIM _
        (aux_hpMapCoraCex_quadMapMatZono _ _ rfl fun j => j.elim0).2 fun i j => by
          rw [(aux_hpMapCoraCex_quadMapMatZono _ _ rfl fun j => j.elim0).1]; simp))
      (aux_hpMapCoraCex_plus (aux_hpMapCoraCex_mtimesIM _
        (aux_hpMapCoraCex_plus (aux_hpMapCoraCex_mtimes _ fun j => j.elim0)
          (aux_hpMapCoraCex_ofPoint _)) fun i j => by
            simp [Interval.radius, Interval.mulLo, Interval.mulHi, Zonotope.halfspaceRange, hG])
        hG)) zo) _ _ hmem) 0
  -- its first coordinate is `k₀ = 1`, the run's `2`
  rw [aux_hpMapCoraCex_reduceGirard_c] at heq
  simp only [Zonotope.plus, Zonotope.mtimes, Zonotope.recentre, Zonotope.mtimesIntervalMat,
    Zonotope.quadMapMatZono, Zonotope.quadMap, Zonotope.halfspaceRange, hc, hG, mulVec_zero,
    add_zero, zero_dotProduct, dotProduct_zero, zero_add, abs_zero, Finset.sum_const_zero,
    sub_zero] at heq
  simp only [Zonotope.ofPoint, GuardMap.hitPoint, show (2 : ℝ) / 2 = 1 by norm_num] at heq
  rw [aux_hpMapCoraCex_b] at heq
  simp [mulVec, dotProduct, Fin.sum_univ_three, aux_hpMapCoraCex_A, vecMulVec, x,
    Matrix.vecHead, Matrix.vecTail, Interval.center, Interval.mulLo, Interval.mulHi] at heq
  norm_num at heq

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
