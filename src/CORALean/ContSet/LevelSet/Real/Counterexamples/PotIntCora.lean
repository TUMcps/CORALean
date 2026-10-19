module

public import CORALean.ContSet.LevelSet.Real.Operations.IsIntersectingCell
public import CORALean.ContSet.LevelSet.Real.Definitions.RangeBound
public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# `potInt`'s scan over level-set guards, as CORA runs it

CORA's `@location/potInt.m` loops over the guards `i` and the reach sets `j` and lists `(i, j)`
when `isIntersecting_(guardSet,Rset{j},'approx',1e-8)`. Here each guard is a level set, so the
test is `LevelSet.isIntersecting_cell` at tolerance `1e-8` on the bounds `B guardSet j` of the
guard function over set `j` (assumed a range bound, as there). The list is the set of listed
index pairs, 0-based. Not modelled: the skip of transitions into `finalLoc`, and the final step
that swaps a lone hyperplane hit for the next time-point set.

# CORA's `potInt` misses a guard that is hit

The guard `{x | x = 0 ∧ x - 1 ≤ 0}` (a cell `{'==','<='}`) and the reach set `[0, 1]` share the
point `0`, yet the `==` row has bounds `(0, 1)`, which `isIntersecting_` reads as `0 < 0`, so
`potInt` does not list the pair `(0, 0)` and the jump through this guard is missed (read from the
source, not run). The bounds are range bounds of the guard function over the set.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
def LevelSet.potIntCora (guards : List (LevelSet n)) (nSets : ℕ)
    (B : (g : LevelSet n) → ℕ → Fin g.m → Interval ℝ) : Set (ℕ × ℕ) :=
  {p | ∃ i : p.1 < guards.length,
    let guardSet := guards[p.1]
    p.2 < nSets ∧ LevelSet.isIntersecting_cell (1 / 10 ^ 8) guardSet.op (B guardSet p.2)}

end CORALean.Real

namespace CORALean.Real

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The guard `x = 0 ∧ x - 1 ≤ 0`. -/
def LevelSet.aux_G : LevelSet 1 :=
  ⟨2, fun x i => if i = 0 then x 0 else x 0 - 1, fun i => if i.val = 0 then .eq else .le⟩

/-- The reach set `[0, 1]`. -/
def LevelSet.aux_R : Interval (Vec ℝ 1) := ⟨fun _ => 0, fun _ => 1⟩

/-- The bounds of the guard function over `[0, 1]`: `(0, 1)` and `(-1, 0)`. -/
def LevelSet.aux_BG (g : LevelSet 1) (_ : ℕ) : Fin g.m → Interval ℝ :=
  fun i => if i.val = 0 then ⟨0, 1⟩ else ⟨-1, 0⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem LevelSet.potIntCora_misses_counterexample : -- --- CONCL ---
    LevelSet.aux_G.construct ∩ LevelSet.aux_R.construct ≠ ∅ ∧
      (∀ i : Fin 2, IsRangeBound (fun x => LevelSet.aux_G.f x i) LevelSet.aux_R.construct
        (LevelSet.aux_BG LevelSet.aux_G 0 i).inf (LevelSet.aux_BG LevelSet.aux_G 0 i).sup) ∧
      (0, 0) ∉ LevelSet.potIntCora [LevelSet.aux_G] 1 LevelSet.aux_BG := by -- --- PROOF ---
  refine ⟨?_, ?_, ?_⟩
  · -- the point `0` is in both
    intro h
    have : (fun _ => (0 : ℝ) : Vec ℝ 1) ∈ (∅ : Set (Vec ℝ 1)) := by
      rw [← h]
      refine ⟨?_, fun i => ⟨le_rfl, zero_le_one⟩⟩
      show ∀ i : Fin 2, _
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩ <;> simp [LevelSet.aux_G, CompOp.holds]
    exact this
  · -- the bounds are range bounds
    refine Fin.forall_fin_two.mpr ⟨fun x hx => ?_, fun x hx => ?_⟩
    · have h0 := hx 0
      simp only [LevelSet.aux_BG, LevelSet.aux_G]
      exact ⟨h0.1, h0.2⟩
    · have h0 := hx 0
      have h1 : (0 : ℝ) ≤ x 0 := h0.1
      have h2 : x 0 ≤ 1 := h0.2
      simp only [LevelSet.aux_BG, LevelSet.aux_G]
      exact ⟨by simp; linarith, by simp; linarith⟩
  · -- the `==` row reads `0 < 0`
    rintro ⟨_, _, h⟩
    have := h (⟨0, by decide⟩ : Fin 2)
    simp [LevelSet.aux_G, LevelSet.aux_BG] at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
