module

public import CORALean.Global.Float.Instances.Binary64.Definitions.IsTrustedHardware
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Order.Preorder.Finite

@[expose] public section

/-!
# No type of 2 ^ 64 values is trusted hardware

`IsTrustedHardware` cannot hold, of this machine or any other: `toReal` reads a `Float` through its
64 bits, so it takes finitely many values and has a largest, `M ≥ toReal 1.0 = 1`, at some `x`;
`add_le_addUp x x` then asks `2 M ≤ toReal (addUp x x) ≤ M`. So `trustedHardware` proves `False`,
and a theorem resting on it says nothing; this is the proof, which uses no axiom of the library.
The same holds of every `SoundFloatArithmetic` scalar with finitely many values, which is why the
proved finite formats (`IEEE`) keep an unbounded exponent. README, "The trust base", says what the
runs at `Float` rest on instead.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* `IsTrustedHardware` does not hold
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Binary64


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `UInt64` has finitely many values, by `toNat` into `Fin (2 ^ 64)`. -/
private theorem aux_finite_uInt64 : Finite UInt64 :=
  Finite.of_injective (fun u : UInt64 => (⟨u.toNat, u.toNat_lt⟩ : Fin (2 ^ 64)))
    (fun _ _ h => UInt64.toNat_inj.mp (Fin.mk.inj_iff.mp h))

/-- `toReal` takes finitely many values: it reads `toBits` alone. -/
private theorem aux_finite_range : -- --- CONCL ---
    (Set.range toReal).Finite := by -- --- PROOF ---
  haveI := aux_finite_uInt64
  classical
  let g : UInt64 → ℝ := fun u => if h : ∃ x : Float, x.toBits = u then toReal h.choose else 0
  refine (Set.finite_range g).subset ?_
  rintro _ ⟨x, rfl⟩
  refine ⟨x.toBits, ?_⟩
  have hx : ∃ y : Float, y.toBits = x.toBits := ⟨x, rfl⟩
  simp only [g, dif_pos hx]
  -- the chosen float has the same bits, so the same decoding
  unfold toReal toDyadic sign expField sigField
  rw [hx.choose_spec]


-- =======================================  MAIN THEOREM  ======================================= --

theorem not_isTrustedHardware : -- --- CONCL ---
    ¬ IsTrustedHardware := by -- --- PROOF ---
  intro h
  obtain ⟨_, ⟨x, rfl⟩, hmax⟩ := aux_finite_range.exists_maximal ⟨_, ⟨1.0, rfl⟩⟩
  have hle : ∀ y : Float, toReal y ≤ toReal x := fun y =>
    (le_total (toReal y) (toReal x)).elim id (hmax ⟨y, rfl⟩)
  -- `1 ≤ M` and `2 M ≤ M`
  have h1 := hle 1.0
  rw [h.toReal_one] at h1
  linarith [le_trans (h.add_le_addUp x x) (hle _)]

end CORALean.Float.Binary64


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
