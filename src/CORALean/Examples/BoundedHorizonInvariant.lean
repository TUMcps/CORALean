import CORALean.ContSet.Interval.Real.Instances
import CORALean.HybridDynamics.Theorems.RunOnOuter

/-!
# An invariant family that genuinely depends on how many jumps a run has taken

Two locations, `false` and `true`, each transitioning to the other. `R k ℓ` is a
box of radius `k + 1` regardless of `ℓ`, so `R 0 ℓ ≠ R 1 ℓ`: an example with a
constant family would prove nothing about the index `InvariantOn` carries.

`hinv` is proved outright — `flow` from `(HA.loc ℓ).inv`, the radius-`1` box,
sitting inside every wider `R k ℓ`; `jump` from the identity reset carrying a
radius-`(k+1)` point into the radius-`(k+2)` box it lands in. What is *not*
attempted is an actual flowing run: `Location.Trajectory.flow` asks for a
`HasDerivWithinAt` witness, real-analysis machinery this file does not build,
so `run` below is taken as a hypothesis, exactly as round one's `BouncingBall`
already does for `Run`.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

/-- Loops to the other location, guard and reset both trivial. -/
def BHI.trans (b : Bool) : Transition ℐ𝒱 Bool ℝ 1 where
  guard := ⟨![(-1:ℝ)], ![1]⟩
  W := 1
  w := 0
  target := !b

/-- Both locations share the same radius-`1` invariant and zero dynamics; only
`trans` tells them apart. -/
def BHI.loc (b : Bool) : Location ℐ𝒱 ℐ𝒱 Bool ℝ 1 where
  inv := ⟨![(-1:ℝ)], ![1]⟩
  dynamics := ⟨0⟩
  U := ⟨![(0:ℝ)], ![0]⟩
  trans := [BHI.trans b]

def BHI.HA : HybridAutomaton ℐ𝒱 ℐ𝒱 Bool ℝ 1 := ⟨BHI.loc⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Grows with the jump count, the same at both locations. -/
def BHI.R (k : ℕ) (_ : Bool) : Interval (Vec ℝ 1) := ⟨![-((k:ℝ) + 1)], ![(k:ℝ) + 1]⟩

/-- The whole reason the index exists: the family genuinely moves. -/
theorem BHI.R_ne : BHI.R 0 false ≠ BHI.R 1 false := by
  intro h
  have h2 := congrArg (fun I => (I : Interval (Vec ℝ 1)).sup 0) h
  norm_num [BHI.R] at h2

-- `flow` reads off the location's fixed invariant; `jump`, the identity reset.

theorem BHI.hinv : BHI.HA.InvariantOn BHI.R where
  flow {k ℓ τ x u} h h₀ {t} ht := by
    intro i
    rw [show i = 0 from Subsingleton.elim i 0]
    have hb : (BHI.loc ℓ).inv.inf 0 ≤ x t 0 ∧ x t 0 ≤ (BHI.loc ℓ).inv.sup 0 :=
      h.invariant t ht 0
    simp [BHI.loc] at hb
    have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    refine ⟨?_, ?_⟩
    · show (BHI.R k ℓ).inf 0 ≤ x t 0
      simp [BHI.R]
      linarith [hb.1]
    · show x t 0 ≤ (BHI.R k ℓ).sup 0
      simp [BHI.R]
      linarith [hb.2]
  -- the reset is the identity, so `jump` only has to grow the radius by `1`
  jump {k ℓ e} hmem {z} hz hguard := by
    have he : e = BHI.trans ℓ := by simpa [BHI.loc, BHI.HA] using hmem
    subst he
    have hreset : (BHI.trans ℓ).reset z = z := by
      simp [Transition.reset, BHI.trans, Matrix.one_mulVec]
    rw [hreset]
    intro i
    rw [show i = 0 from Subsingleton.elim i 0]
    have hzb : (BHI.R k ℓ).inf 0 ≤ z 0 ∧ z 0 ≤ (BHI.R k ℓ).sup 0 := hz 0
    simp [BHI.R] at hzb
    refine ⟨?_, ?_⟩
    · show (BHI.R (k + 1) (BHI.trans ℓ).target).inf 0 ≤ z 0
      simp [BHI.R]
      linarith [hzb.1]
    · show z 0 ≤ (BHI.R (k + 1) (BHI.trans ℓ).target).sup 0
      simp [BHI.R]
      linarith [hzb.2]

/-- The one thing the whole file is for: a run known only through its jump
count lands where `InvariantOn`, read at the count reached, says it must. -/
example {m k : ℕ} {ℓ ℓ' : Bool} {x y : Vec ℝ 1} (run : BHI.HA.RunOn m ℓ x ℓ' y)
    (hx : x ∈ construct (BHI.R k ℓ)) : y ∈ construct (BHI.R (k + m) ℓ') :=
  run.mem_of_invariantOn BHI.hinv hx

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
