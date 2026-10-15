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
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in the generator count. -/
theorem Zonotope.absCost_mono {h h' : ℕ} (n : ℕ) (hh : h ≤ h') :
    Zonotope.absCost n h ≤ Zonotope.absCost n h' :=
  Nat.mul_le_mul_left _ (Nat.succ_le_succ hh)


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
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in the generator count. -/
theorem Zonotope.minkDiffAlignedCost_mono {h h' : ℕ} (n : ℕ) (hh : h ≤ h') :
    Zonotope.minkDiffAlignedCost n h ≤ Zonotope.minkDiffAlignedCost n h' :=
  Nat.mul_le_mul_left _ (Nat.succ_le_succ hh)


-- ===========================  `Zonotope.minkDiffStretchCost_mono`  ============================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in the generator count. -/
theorem Zonotope.minkDiffStretchCost_mono {h h' : ℕ} (n : ℕ) (hh : h ≤ h') :
    Zonotope.minkDiffStretchCost n h ≤ Zonotope.minkDiffStretchCost n h' :=
  Nat.mul_le_mul_left _ (Nat.succ_le_succ hh)


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


-- ===============================  `Zonotope.quadMapCost_mono`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in the generator count. -/
theorem Zonotope.quadMapCost_mono {h h' : ℕ} (m n : ℕ) (hh : h ≤ h') :
    Zonotope.quadMapCost m n h ≤ Zonotope.quadMapCost m n h' :=
  Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.succ_le_succ hh) 2))


-- ===============================  `Zonotope.reduceByCost_mono`  =============================== --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in the absorbed count, so a bound on how many generators a split
throws away gives a bound on the cost. -/
theorem Zonotope.reduceByCost_mono {r r' : ℕ} (n : ℕ) (hle : r ≤ r') :
    Zonotope.reduceByCost n r ≤ Zonotope.reduceByCost n r' :=
  Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hle)


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
