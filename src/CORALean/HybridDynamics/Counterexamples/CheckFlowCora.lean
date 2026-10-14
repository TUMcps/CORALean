module

public import CORALean.HybridDynamics.Definitions.Location
public import CORALean.ContSet.Zonotope.Real.Instances
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import CORALean.HybridDynamics.Theorems.CheckFlowDropped

@[expose] public section

/-!
# `Location.checkFlowCora`: CORA's `checkFlow` as printed, with the vector offset

CORA's `@location/checkFlow.m` at a hyperplane guard `{x | c·x = d}` and a `linearSys`
`ẋ = A x + B u + sys.c`, `u ∈ [uLo, uHi]`, the linear branch of `aux_flowInDirection`, one `let`
per MATLAB line. `A` is the location's; `B` and `off` (`sys.c`) are passed beside it, since
`Location` folds them into `U`. The last summand of `flow = cA*cen + (cA*G)*I +
(c*sys.B)*interval(params.U) + sys.c` is the `n×1` vector `sys.c`, so `res` is a vector and `if
res` holds only if every entry `… + sys.c(i)` of the supremum is positive. That is kept.

`@location/guardIntersect.m` runs `[res,P{i}] = checkFlow(loc,guard,P{i},params)` on each group
of time-interval sets meeting a hyperplane or level-set guard and skips the group if `res` is
false: the sets dropped here are never intersected with the guard.

Left out: `c = guard.Ae ./ norm(guard.Ae)` and `aux_adaptGuard` (`c` is the outward unit normal,
as for `Location.checkFlow`); `E*params.w` (no `E`); and `R = B * reduce(B'*Rproj,'pca',1)`,
which leaves `Rproj` unchanged when it has at most `n` generators and encloses it otherwise.

# CORA's `checkFlow` drops a set the bouncing ball leaves through the guard

The bouncing ball `ẋ₁ = x₂`, `ẋ₂ = -g` (CORA: `A = [0 1; 0 0]`, `sys.c = [0; -g]`, no input),
invariant `x₁ ≥ 0`, guard `x₁ = 0` with outward normal `c = (-1, 0)`, and the box
`R = [0, 1] × [-1, 1]` as the time-interval set meeting the guard, for any `g ≥ 1`.

CORA's fast test sees the flow `c·(A·(0, 0) + sys.c) = 0` at the centre of the projection and
fails; the second test bounds `c·A x = -x₂` over the projection by `1` and adds `sys.c`
entrywise, `(1 + 0, 1 - g)`, whose second entry is not positive, so `checkFlowCora` drops `R`.
The projection has two generators in two dimensions, so CORA's `'pca'` reduction left out of
`checkFlowCora` changes nothing here. `guardIntersect` then skips `R`: the jump from it is
missed, and with it every state after.

Yet the run from `(1/(2g), 0)`, `x(t) = (1/(2g) - g t²/2, -g t)`, stays in `R` and in the
invariant and reaches the guard at `t = 1/g`, in `(0, -1)`. The tree's `Location.checkFlow` keeps
`R` (by `Location.checkFlow_dropped`, the flow at `(0, -1)` points out).
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar
open scoped CORALean.Real

variable {G : ℕ → Type} [∀ n, ContSet (G n) (Vec ℝ n)] {L : Type} {n m : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's `checkFlow`, linear branch, as printed: the reach sets kept, `sys.c` added entrywise. -/
noncomputable def Location.checkFlowCora (ℓ : Location 𝒵 G L ℝ n)
    (B : Mat ℝ n m) (off : Vec ℝ n) (uLo uHi : Vec ℝ m) (c : Vec ℝ n) (d : ℝ)
    (Rs : List (Real.Zonotope (Vec ℝ n))) : List (Real.Zonotope (Vec ℝ n)) :=
  open Classical in Rs.filter fun R =>
    let A : Mat ℝ n n := toRealMat ℓ.dynamics.A
    -- Rproj = projectOnHyperplane(R,guard): the map (I - c cᵀ) x + d c
    let P : Mat ℝ n n := 1 - vecMulVec c c
    let Rproj : Real.Zonotope (Vec ℝ n) := ⟨R.h, P *ᵥ R.c + d • c, fun j => P *ᵥ R.G j⟩
    -- params.u = center(params.U)
    let u : Vec ℝ m := (1 / 2 : ℝ) • (uLo + uHi)
    -- flow = fcnHan(0,center(Rproj)), with fcnHan = A*x + B*params.u + sys.c
    let flow₀ : Vec ℝ n := A *ᵥ Rproj.c + B *ᵥ u + off
    -- flow = c*flow
    let flowC : ℝ := c ⬝ᵥ flow₀
    -- cen = center(R); G = generators(R)   (R = Rproj, the 'pca' box step left out)
    let cen : Vec ℝ n := Rproj.c
    let Gs : Fin Rproj.h → Vec ℝ n := Rproj.G
    -- cA = c*sys.A
    let cA : Vec ℝ n := Aᵀ *ᵥ c
    -- flow = cA*cen + (cA*G)*I + (c*sys.B)*interval(params.U) + sys.c, its supremum entrywise
    let cB : Vec ℝ m := Bᵀ *ᵥ c
    let flowSup : Vec ℝ n := fun i =>
      cA ⬝ᵥ cen + ∑ j, |cA ⬝ᵥ Gs j| + ∑ k, max (cB k * uLo k) (cB k * uHi k) + off i
    -- if flow > 0 (fast check), else res = supremum(interval(flow)) > 0, `if res`: every entry
    (0 < flowC ∨ ∀ i, 0 < flowSup i : Prop)

end CORALean

namespace CORALean

open Matrix Scalar
open scoped CORALean.Real

variable {G : ℕ → Type} [∀ n, ContSet (G n) (Vec ℝ n)] {L : Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- CORA drops a reach set that a run leaves through the guard; the tree's `checkFlow` keeps it. -/
theorem Location.checkFlowCora_drops_hit_counterexample
    (ℓ : Location 𝒵 G L ℝ 2) {g : ℝ} (hg : 1 ≤ g)
    (hA : ℓ.dynamics.A = !![0, 1; 0, 0]) (hU : ![0, -g] ∈ ContSet.construct ℓ.U)
    (hinv : ∀ x : Vec ℝ 2, 0 ≤ x 0 → x ∈ ContSet.construct ℓ.inv) :
    let R : Real.Zonotope (Vec ℝ 2) := ⟨2, ![1 / 2, 0], ![![1 / 2, 0], ![0, 1]]⟩
    let c : Vec ℝ 2 := ![-1, 0]
    R ∉ ℓ.checkFlowCora (0 : Mat ℝ 2 0) ![0, -g] 0 0 c 0 [R] ∧
      R ∈ ℓ.checkFlow c 0 [R] ∧
      ∃ τ x u, ℓ.Trajectory τ x u ∧ (∀ t ∈ Set.Icc 0 τ, x t ∈ R.construct) ∧
        c ⬝ᵥ x τ = 0 := by -- --- PROOF ---
  intro R c
  have hg0 : 0 < g := by linarith
  refine ⟨?_, ?_, ?_⟩
  -- CORA: the fast test sees `0`, the second test `(1, 1 - g)`
  · have hP : (1 - vecMulVec c c : Mat ℝ 2 2) = !![0, 0; 0, 1] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [c, vecMulVec]
    simp only [Location.checkFlowCora, List.mem_filter, List.mem_singleton, true_and,
      decide_eq_true_eq, not_or, not_forall, not_lt, hP, hA]
    refine ⟨?_, 1, ?_⟩
    · simp [R, c, dotProduct, Fin.sum_univ_two]
    · simp [R, c, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.transpose_apply]
      linarith
  -- the tree: the flow at `(0, -1)` of `R` points out
  · by_contra hdrop
    have hx : (![0, -1] : Vec ℝ 2) ∈ (R : Real.Zonotope (Vec ℝ 2)).construct :=
      ⟨![-1, -1], by intro j; fin_cases j <;> simp, by
        funext i; fin_cases i <;> simp [R, Fin.sum_univ_two]⟩
    have h := Location.checkFlow_dropped ℓ c 0 [R] (List.mem_singleton_self R) hdrop hx hU
    simp [c, hA, dotProduct, Fin.sum_univ_two] at h
    linarith
  -- the run from `(1/(2g), 0)` reaches the guard at `t = 1/g`
  · refine ⟨1 / g, fun t => ![1 / (2 * g) - g * t ^ 2 / 2, -(g * t)], fun _ => ![0, -g],
      ⟨by positivity, fun _ _ => hU, ?_, ?_⟩, ?_, ?_⟩
    · intro t _
      refine (hasDerivAt_pi.2 fun i => ?_).hasDerivWithinAt
      fin_cases i
      -- position: `d/dt (1/(2g) - g t²/2) = -g t`, the velocity
      · have h := HasDerivAt.const_sub (1 / (2 * g))
          (HasDerivAt.const_mul (g / 2) (hasDerivAt_pow 2 t))
        have e : (fun s : ℝ => 1 / (2 * g) - g / 2 * s ^ 2) =
            fun s => 1 / (2 * g) - g * s ^ 2 / 2 := by
          funext s; ring
        rw [e] at h
        show HasDerivAt (fun s : ℝ => 1 / (2 * g) - g * s ^ 2 / 2) _ t
        refine HasDerivAt.congr_deriv h ?_
        simp [hA]
        ring
      -- velocity: `d/dt (-g t) = -g`, the offset
      · show HasDerivAt (fun s : ℝ => -(g * s)) _ t
        refine HasDerivAt.congr_deriv (HasDerivAt.neg (HasDerivAt.const_mul g (hasDerivAt_id t))) ?_
        simp [hA]
    -- the invariant `x₁ ≥ 0`: `g t² ≤ 1/g` up to `t = 1/g`
    · intro t ht
      have h1 : g * t ≤ 1 := by
        have := ht.2; rw [le_div_iff₀ hg0] at this; linarith
      have h2 : g * t ^ 2 ≤ g⁻¹ := by
        rw [← one_div, le_div_iff₀ hg0]
        nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg hg0.le ht.1)]
      apply hinv
      simp
      linarith
    · intro t ht
      have h1 : g * t ≤ 1 := by
        have := ht.2; rw [le_div_iff₀ hg0] at this; linarith
      have h2 : g * t ^ 2 ≤ g⁻¹ := by
        rw [← one_div, le_div_iff₀ hg0]
        nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg hg0.le ht.1)]
      have hgi : g⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hg
      have hgp : 0 < g⁻¹ := inv_pos.2 hg0
      have h3 : 0 ≤ g * t := mul_nonneg hg0.le ht.1
      have h4 : 0 ≤ g * t ^ 2 := by positivity
      -- the factors of the two generators
      refine ⟨![g⁻¹ - g * t ^ 2 - 1, -(g * t)], ?_, ?_⟩
      · intro j
        fin_cases j
        · show |g⁻¹ - g * t ^ 2 - 1| ≤ 1
          rw [abs_le]; constructor <;> linarith
        · show |-(g * t)| ≤ 1
          rw [abs_le]; constructor <;> linarith
      · funext i
        fin_cases i
        · simp [R, Fin.sum_univ_two]
          field_simp
          ring
        · simp [R, Fin.sum_univ_two]
    -- on the guard at `t = 1/g`
    · simp [c, dotProduct, Fin.sum_univ_two]
      field_simp
      ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
