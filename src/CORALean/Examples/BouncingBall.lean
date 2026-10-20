import CORALean.ContSet.Conversion.Real.Instances
import CORALean.ContDynamics.LinearSys.Operations.OfABc
import CORALean.ContSet.HPolytope.Real.Instances
import CORALean.ContSet.HPolytope.Real.Operations.MemSlabIff
import CORALean.ContSet.Zonotope.Real.Instances
import CORALean.HybridDynamics.Theorems.FlowOuter
import CORALean.HybridDynamics.Theorems.HoldsOfRun
import CORALean.HybridDynamics.Theorems.InvariantOfEnclosureCut
import CORALean.HybridDynamics.Theorems.JumpOuter
import CORALean.ContSet.Conversion.Real.Operations.Basic
import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Zonotope

/-!
# A bouncing ball, as a hybrid automaton

The textbook automaton: one location, one transition back into it. The state is
`(position, velocity)`, the dynamics CORA's `linearSys(A, B, c)` with `A = [0 1; 0 0]`, `B = 0`,
`c = [0; -g]`, gravity the offset; the reset flips the velocity and damps it by `d`. Two
representations at once (#39): the reachable set is a `Zonotope`, the guard and the invariant are
`HPolytope`s, the guard the unbounded halfspace description `p = 0 ∧ v ≤ 0`. `ballZono` is the
invariant said again as a zonotope, `bounceCut` the guard intersection `jump_outer` asks for. The
result is `bouncingBall_invariant`: the box `[0, p] × [-v, v]` is kept at every dwell time and
across every bounce, exactly when the damping is at most one.

## Inputs
* `g` – gravity
* `d` – damping factor
* `p` – maximal position
* `v` – maximal velocity

## Output
* bouncing ball automaton
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar NormedSpace MeasureTheory Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {d p v : ℝ}

/-- The floor met from above, `p = 0 ∧ v ≤ 0`: an equality row and an
inequality row, and unbounded, so no zonotope denotes it. -/
noncomputable def Example.floorGuard : HPolytope (Vec ℝ 2) where
  m := 1
  A := ![LinearMap.proj 1]
  b := ![0]
  me := 1
  Ae := ![LinearMap.proj 0]
  be := ![0]

/-- The box `[0, p] × [-v, v]` the ball stays in, as the slab it is. -/
noncomputable def Example.ballBox (p v : ℝ) : HPolytope (Vec ℝ 2) :=
  HPolytope.slab (1 : Mat ℝ 2 2) ![0, -v] ![p, v]

/-- The bounce: on the floor moving down, keep the position and reverse the
velocity, damped by `d`. -/
noncomputable def Example.bounce (d : ℝ) : Transition ℋ𝒫 Unit ℝ 2 where
  guard := Example.floorGuard
  W := !![1, 0; 0, -d]
  w := 0
  target := ()


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Falling under gravity inside the box `[0, p] × [-v, v]`, and bouncing out of
the only location back into it. -/
noncomputable def Example.bouncingBall (g d p v : ℝ) : HybridAutomaton 𝒵 ℋ𝒫 Unit ℝ 2 where
  loc _ :=
    { inv := Example.ballBox p v
      dynamics := LinearSys.ofABc !![0, 1; 0, 0] (0 : Mat ℝ 2 1) ![0, -g]
      U := ⟨0, ![0], ![]⟩
      W := ⟨0, ![0], ![]⟩
      trans := [Example.bounce d] }

/-- The same box as `ballBox`, in the state's representation: what `R` has to
be, the invariant being in the guard's. -/
noncomputable def Example.ballZono (p v : ℝ) : Zonotope (Vec ℝ 2) :=
  ⟨2, ![p / 2, 0], ![![p / 2, 0], ![0, v]]⟩

/-- The box cut down to the guard: on the floor, falling at a speed of at most
`v`. This is the `Rg` that `jump_outer` asks a caller to name. -/
noncomputable def Example.bounceCut (v : ℝ) : Zonotope (Vec ℝ 2) :=
  ⟨1, ![0, -v / 2], ![![0, v / 2]]⟩

/-- The reset image of the cut set, in coordinates: the floor, left with an
upward velocity of at most `d v`. -/
theorem Example.mem_bounce_jump_cut {x : Vec ℝ 2}
    (hx : x ∈ construct ((Example.bounce d).jump (S := 𝒵) (Example.bounceCut v))) :
    ∃ s : ℝ, |s| ≤ 1 ∧ x = ![0, d * v / 2 - d * v / 2 * s] := by -- --- PROOF ---
  replace hx : x ∈ (Zonotope.mtimes (Example.bounce d).W (Example.bounceCut v)).construct
      + ((Interval.point (toRealVec (Example.bounce d).w)).zonotope).construct := by
    rw [Zonotope.plus_exact]; exact hx
  rw [← Zonotope.mtimes_exact] at hx
  obtain ⟨a, ⟨z, ⟨β, hβ, rfl⟩, rfl⟩, b, ⟨γ, -, rfl⟩, rfl⟩ := hx
  refine ⟨β ⟨0, Nat.zero_lt_one⟩, hβ _, ?_⟩
  funext i
  fin_cases i
  · simp [Example.bounce, Example.bounceCut, Interval.point, Interval.zonotope]
  · simp [Example.bounce, Example.bounceCut, Interval.point, Interval.zonotope]
    ring

/-- The invariant said as a slab sits inside the same box said as a zonotope:
the two representations, related where the criterion needs them related. -/
theorem Example.ballZono_contains_ballBox (hp : 0 < p) (hv : 0 < v) :
    construct (Example.ballBox p v) ⊆ construct (Example.ballZono p v) := by -- --- PROOF ---
  intro x hx
  -- the slab's rows, read back as the four scalar bounds
  have hx' : x ∈ (HPolytope.slab (1 : Mat ℝ 2 2) ![0, -v] ![p, v]).construct := hx
  obtain ⟨h0a, h0b⟩ := HPolytope.mem_slab_iff.mp hx' 0
  obtain ⟨h1a, h1b⟩ := HPolytope.mem_slab_iff.mp hx' 1
  simp only [Matrix.one_mulVec, Matrix.cons_val_zero, Matrix.cons_val_one] at h0a h0b h1a h1b
  -- one generator per coordinate, so each factor is that coordinate's bound rescaled
  show _ ∈ Zonotope.construct (⟨2, ![p / 2, 0], ![![p / 2, 0], ![0, v]]⟩ : Zonotope (Vec ℝ 2))
  refine ⟨![(2 * x 0 - p) / p, x 1 / v], Fin.forall_fin_two.2 ⟨?_, ?_⟩, ?_⟩
  · show |(2 * x 0 - p) / p| ≤ 1
    rw [abs_div, abs_of_pos hp, div_le_one hp, abs_le]
    constructor <;> linarith
  · show |x 1 / v| ≤ 1
    rw [abs_div, abs_of_pos hv, div_le_one hv, abs_le]
    constructor <;> linarith
  · funext i
    fin_cases i
    · simp [Fin.sum_univ_two]
      field_simp
      ring
    · simp [Fin.sum_univ_two]
      field_simp

/-- The `hand` bargain discharged at this automaton: the box met by the floor is
the cut set, an inclusion stated across the two representations. -/
theorem Example.ballZono_inter_guard (hv : 0 < v) :
    construct (Example.ballZono p v) ∩ construct Example.floorGuard
      ⊆ construct (Example.bounceCut v) := by -- --- PROOF ---
  rintro x ⟨hz, hg⟩
  -- the guard pins the position and signs the velocity; the box bounds it below
  obtain ⟨hle, heq⟩ := hg
  have h0 : x 0 = 0 := by simpa [Example.floorGuard] using heq (0 : Fin 1)
  have h1 : x 1 ≤ 0 := by simpa [Example.floorGuard] using hle (0 : Fin 1)
  have hz' : x ∈ Zonotope.construct
      (⟨2, ![p / 2, 0], ![![p / 2, 0], ![0, v]]⟩ : Zonotope (Vec ℝ 2)) := hz
  obtain ⟨β, hβ, hx⟩ := hz'
  have hxv : x 1 = β 1 * v := by
    have h := congrFun hx 1
    simpa [Fin.sum_univ_two] using h
  have hlow : -v ≤ x 1 := by
    have hβ1 := abs_le.mp (hβ 1)
    rw [hxv]
    nlinarith [hβ1.1, hv]
  -- one generator left, and the velocity is all it carries
  show _ ∈ Zonotope.construct (⟨1, ![0, -v / 2], ![![0, v / 2]]⟩ : Zonotope (Vec ℝ 2))
  refine ⟨![(2 * x 1 + v) / v], Fin.forall_fin_one.2 ?_, ?_⟩
  · show |(2 * x 1 + v) / v| ≤ 1
    rw [abs_div, abs_of_pos hv, div_le_one hv, abs_le]
    constructor <;> linarith
  · funext i
    fin_cases i
    · simpa using h0
    · simp
      field_simp
      ring

/-- The criterion at this automaton: the box is an inductive invariant, the flow
half discharged by the cut and the jump half by the damping being at most one. -/
theorem Example.bouncingBall_invariant (g : ℝ) (hp : 0 < p) (hv : 0 < v)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    (Example.bouncingBall g d p v).Invariant
      (fun _ => Example.ballZono p v) := by -- --- PROOF ---
  refine HybridAutomaton.invariant_of_enclosure_cut _ _ (fun ℓ τ _ => ?_) (fun ℓ e he => ?_)
  · -- the cut is the whole flow obligation: whatever the dwell time, the part
    -- of the enclosure still inside the invariant is inside the box
    refine ⟨⌈‖τ • toRealMat ((Example.bouncingBall g d p v).loc ℓ).dynamics.A‖⌉₊, ?_,
      Set.inter_subset_right.trans (Example.ballZono_contains_ballBox hp hv)⟩
    rw [div_lt_one (by positivity)]
    push_cast
    linarith [Nat.le_ceil ‖τ • toRealMat ((Example.bouncingBall g d p v).loc ℓ).dynamics.A‖]
  · -- the bounce is the only transition, `bounceCut` the enclosure `jump_outer`
    -- asks for, and the reset image sits in the box exactly when `d ≤ 1`
    simp only [Example.bouncingBall, List.mem_singleton] at he
    subst he
    refine ⟨Example.bounceCut v, Example.ballZono_inter_guard hv, fun x hx => ?_⟩
    obtain ⟨s, hs, rfl⟩ := Example.mem_bounce_jump_cut hx
    rw [abs_le] at hs
    show _ ∈ Zonotope.construct (⟨2, ![p / 2, 0], ![![p / 2, 0], ![0, v]]⟩ : Zonotope (Vec ℝ 2))
    refine ⟨![-1, d * (1 - s) / 2], Fin.forall_fin_two.2 ⟨by simp, ?_⟩, ?_⟩
    · show |d * (1 - s) / 2| ≤ 1
      rw [abs_le]
      constructor <;> nlinarith [hs.1, hs.2]
    · funext i
      fin_cases i
      · simp [Fin.sum_univ_two]
      · simp [Fin.sum_univ_two]
        ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
