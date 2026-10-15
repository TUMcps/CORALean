module

public import CORALean.ContSet.Zonotope.Real.Operations.Abs
public import CORALean.Global.Cost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.AbsCost
public import CORALean.ContSet.Zonotope.Real.Operations.Bilin
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.BilinCost
public import CORALean.ContSet.Zonotope.Real.Operations.Map
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.MapCost
public import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffAligned
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.MinkDiffAlignedCost
public import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffStretch
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.MinkDiffStretchCost
public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.MtimesCost
public import CORALean.ContSet.Zonotope.Real.Operations.MtimesMatZonotope
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.MtimesMatZonotopeCost
public import CORALean.ContSet.Zonotope.Real.Operations.Plus
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.PlusCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ImageEnclosureCost
public import CORALean.ContSet.Zonotope.Real.Definitions.SetBasedNetForward
public import CORALean.ContSet.Zonotope.Real.Operations.SetBasedNetDepth
public import CORALean.ContSet.Zonotope.Real.Operations.SetBasedNetMaxWidth
public import CORALean.ContSet.Zonotope.Real.Operations.SetBasedNetNeurons
public import Mathlib.Tactic.Ring
public import CORALean.ContSet.Zonotope.Real.Operations.QuadMap
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.QuadMapCost
public import CORALean.ContSet.Zonotope.Real.Operations.ReduceBy
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ReduceByCost
public import CORALean.ContSet.Zonotope.Real.Operations.Rotate
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.RotateCost

@[expose] public section

/-!
# `ContSet/Zonotope/Real/Complexity/Time/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real


-- ==============================  `SetBasedNet.mul_mul_le_of_le`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `a b h ≤ N N Q` for `a, b ≤ N` and `h ≤ Q`. -/
theorem SetBasedNet.mul_mul_le_of_le {a b h N Q : ℕ} (ha : a ≤ N) (hb : b ≤ N) (hh : h ≤ Q) :
    a * b * h ≤ N * N * Q :=
  Nat.mul_le_mul (Nat.mul_le_mul ha hb) hh


-- =================================  `Zonotope.absCost_mono`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---

/-- Monotone in the generator count. -/
theorem Zonotope.absCost_mono {h h' : ℕ} (n : ℕ) (hh : h ≤ h') :
    Zonotope.absCost n h ≤ Zonotope.absCost n h' := by
  cost_mono [Zonotope.absCost]


-- ================================  `Zonotope.bilinCost_mono`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in both generator counts. -/
theorem Zonotope.bilinCost_mono {h₁ h₁' h₂ h₂' : ℕ} (cf : Cost) (h : h₁ ≤ h₁') (h' : h₂ ≤ h₂') :
    Zonotope.bilinCost cf h₁ h₂ ≤ Zonotope.bilinCost cf h₁' h₂' :=
  Nat.mul_le_mul_right _ (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left h _) h')
    (Nat.mul_le_mul h h'))


-- ============================  `Zonotope.imageEnclosureCost_mono`  ============================ --
-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---

/-- Monotone in the generator count. -/
theorem Zonotope.imageEnclosureCost_mono {q q' : ℕ} (n : ℕ) (cNeuron : Cost) (hq : q ≤ q') :
    Zonotope.imageEnclosureCost n q cNeuron ≤ Zonotope.imageEnclosureCost n q' cNeuron := by
  cost_mono [Zonotope.imageEnclosureCost, Zonotope.mtimesCost, Zonotope.plusCost]


-- =================================  `Zonotope.mapCost_mono`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in the generator count, so a bound on the operand's size gives a
bound on the cost. -/
theorem Zonotope.mapCost_mono {h h' : ℕ} (cf : Cost) (hh : h ≤ h') :
    Zonotope.mapCost cf h ≤ Zonotope.mapCost cf h' :=
  Nat.mul_le_mul_right _ (Nat.succ_le_succ hh)


-- ===========================  `Zonotope.minkDiffAlignedCost_mono`  ============================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---

/-- Monotone in the generator count. -/
theorem Zonotope.minkDiffAlignedCost_mono {h h' : ℕ} (n : ℕ) (hh : h ≤ h') :
    Zonotope.minkDiffAlignedCost n h ≤ Zonotope.minkDiffAlignedCost n h' := by
  cost_mono [Zonotope.minkDiffAlignedCost]


-- ===========================  `Zonotope.minkDiffStretchCost_mono`  ============================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---

/-- Monotone in the generator count. -/
theorem Zonotope.minkDiffStretchCost_mono {h h' : ℕ} (n : ℕ) (hh : h ≤ h') :
    Zonotope.minkDiffStretchCost n h ≤ Zonotope.minkDiffStretchCost n h' := by
  cost_mono [Zonotope.minkDiffStretchCost]


-- ================================  `Zonotope.mtimesCost_mono`  ================================ --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in the generator count, so a bound on the operand's size gives a
bound on the cost. -/
theorem Zonotope.mtimesCost_mono {h h' : ℕ} (m n : ℕ) (hle : h ≤ h') :
    Zonotope.mtimesCost m n h ≤ Zonotope.mtimesCost m n h' :=
  Nat.mul_le_mul_right _ (Nat.succ_le_succ hle)


-- ==========================  `Zonotope.mtimesMatZonotopeCost_mono`  =========================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in both generator counts. -/
theorem Zonotope.mtimesMatZonotopeCost_mono {m n hM hM' h h' : ℕ} (a : hM ≤ hM') (b : h ≤ h') :
    Zonotope.mtimesMatZonotopeCost m n hM h ≤ Zonotope.mtimesMatZonotopeCost m n hM' h' :=
  Zonotope.bilinCost_mono _ a b


-- =================================  `Zonotope.plusCost_mono`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in both generator counts. -/
theorem Zonotope.plusCost_mono {h₁ h₁' h₂ h₂' : ℕ} (n : ℕ) (h1 : h₁ ≤ h₁') (h2 : h₂ ≤ h₂') :
    Zonotope.plusCost n h₁ h₂ ≤ Zonotope.plusCost n h₁' h₂' := by
  cost_mono [Zonotope.plusCost]


-- ===============================  `Zonotope.quadMapCost_mono`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---

/-- Monotone in the generator count. -/
theorem Zonotope.quadMapCost_mono {h h' : ℕ} (m n : ℕ) (hh : h ≤ h') :
    Zonotope.quadMapCost m n h ≤ Zonotope.quadMapCost m n h' := by
  cost_mono [Zonotope.quadMapCost]


-- ===============================  `Zonotope.reduceByCost_mono`  =============================== --
-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---

/-- Monotone in the kept and the absorbed count, so a bound on how many generators a split keeps
and throws away gives a bound on the cost. -/
theorem Zonotope.reduceByCost_mono {q q' r r' : ℕ} (n : ℕ) (hq : q ≤ q') (hr : r ≤ r') :
    Zonotope.reduceByCost n q r ≤ Zonotope.reduceByCost n q' r' := by
  cost_mono [Zonotope.reduceByCost]


-- ================================  `Zonotope.rotateCost_mono`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in the generator count. -/
theorem Zonotope.rotateCost_mono {h h' : ℕ} (n : ℕ) (hh : h ≤ h') :
    Zonotope.rotateCost n h ≤ Zonotope.rotateCost n h' :=
  Cost.add_le_add (le_refl _) (Zonotope.mtimesCost_mono n n hh)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
