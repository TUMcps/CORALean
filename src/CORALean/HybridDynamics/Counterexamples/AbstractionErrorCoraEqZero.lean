module

public import CORALean.HybridDynamics.Counterexamples.AbstractionErrorCora
public import CORALean.ContSet.Zonotope.Real.Operations.RadiusReach
public import CORALean.ContSet.Zonotope.Real.Operations.AbsBound
public import CORALean.ContSet.Interval.Real.Operations.Basic

@[expose] public section

/-!
# CORA's printed error set collapses to `{0}` when `Aᵑ = 0`

`GuardMap.abstractionErrorCora` keeps of `err1` only the summand `(Aᵑ/η!)(τ^{η−1}R₀ − th^{η−1}ξ)`,
which vanishes with `Aᵑ`; with no inputs (`U = {0}`) `err2` and `err3` are `{0}`; and with
`W = 0` (the Taylor remainder of `e^{|A|tmax}` zero, as for a nilpotent `|A|`) so are `Ê R₀`
and `Ê tmax U`. Stated on the representation, center and every generator zero, which is what the
counterexamples compute with (`GuardMap.abstractionErrorCora_counterexample`).

## Inputs
* `A` – flow matrix
* `x₀` – initial state
* `th` – expansion time
* `tmax` – final time
* `η` – Taylor order

## Hypotheses
* `hA` – `A` is nilpotent of index `η`
* `hW` – exponential remainder vanishes

## Conclusion
* CORA's error set is the single point zero
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `Z.c = 0` and every generator `0`: the representation of `{0}`. -/
def aux_absErrCora_Zero (Z : Zonotope (Vec ℝ n)) : Prop := Z.c = 0 ∧ ∀ j, Z.G j = 0

theorem aux_absErrCora_ofPoint : aux_absErrCora_Zero (Zonotope.ofPoint (0 : Vec ℝ n)) :=
  ⟨rfl, fun j => j.elim0⟩

theorem aux_absErrCora_recenter {Z : Zonotope (Vec ℝ n)} (h : aux_absErrCora_Zero Z) :
    aux_absErrCora_Zero Z.recenter := ⟨rfl, h.2⟩

theorem aux_absErrCora_plus {Z₁ Z₂ : Zonotope (Vec ℝ n)} (h₁ : aux_absErrCora_Zero Z₁)
    (h₂ : aux_absErrCora_Zero Z₂) : aux_absErrCora_Zero (Z₁.plus Z₂) := by
  refine ⟨by simp [Zonotope.plus, h₁.1, h₂.1], fun j => ?_⟩
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp [Zonotope.plus, h₁.2, h₂.2]

theorem aux_absErrCora_mtimes_zero (Z : Zonotope (Vec ℝ n)) :
    aux_absErrCora_Zero (Zonotope.mtimes (0 : Mat ℝ n n) Z) :=
  ⟨by simp [Zonotope.mtimes], fun j => by simp [Zonotope.mtimes]⟩

/-- An interval matrix applied to `{0}`: `IM.center 0` and radii `rad(IM)|0| = 0`. -/
theorem aux_absErrCora_mtimesIM (IM : Interval (Mat ℝ n n)) {Z : Zonotope (Vec ℝ n)}
    (h : aux_absErrCora_Zero Z) : -- --- CONCL ---
    aux_absErrCora_Zero (Zonotope.mtimesIntervalMat IM Z) := by -- --- PROOF ---
  have hr : ∀ i, Zonotope.radiusReach IM Z i = 0 := fun i => by
    simp [Zonotope.radiusReach, Zonotope.absBound, h.1, h.2]
  refine ⟨by simp [Zonotope.mtimesIntervalMat, h.1], fun j => ?_⟩
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp [Zonotope.mtimesIntervalMat, h.2]
  · ext i
    simp [Zonotope.mtimesIntervalMat, hr]

/-- The interval matrix `[0, 0]` applied to any zonotope. -/
theorem aux_absErrCora_mtimesIM_zero {IM : Interval (Mat ℝ n n)} (hi : IM.inf = 0)
    (hs : IM.sup = 0) (Z : Zonotope (Vec ℝ n)) : -- --- CONCL ---
    aux_absErrCora_Zero (Zonotope.mtimesIntervalMat IM Z) := by -- --- PROOF ---
  have hr : ∀ i, Zonotope.radiusReach IM Z i = 0 := fun i => by
    simp [Zonotope.radiusReach, Interval.radius, hi, hs]
  refine ⟨by simp [Zonotope.mtimesIntervalMat, Interval.center, hi, hs], fun j => ?_⟩
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp [Zonotope.mtimesIntervalMat, Interval.center, hi, hs]
  · ext i
    simp [Zonotope.mtimesIntervalMat, hr]

theorem aux_absErrCora_sumTerms {f : ℕ → Zonotope (Vec ℝ n)}
    (h : ∀ m, aux_absErrCora_Zero (f m)) (k : ℕ) :
    aux_absErrCora_Zero (Zonotope.sumTerms f k) := by
  induction k with
  | zero => exact aux_absErrCora_ofPoint
  | succ k ih => exact aux_absErrCora_plus ih (h k)

/-- A fold that overwrites ends at its last element. -/
theorem aux_absErrCora_foldl {β : Type} (f : ℕ → β) (init : β) (k : ℕ) :
    (List.range (k + 1)).foldl (fun _ m => f m) init = f k := by
  rw [List.range_succ, List.foldl_append]
  rfl


-- =======================================  MAIN THEOREM  ======================================= --

/-- For `U = {0}`, `R₀ = {x₀}`, `Aᵑ = 0` and `W = 0`, `GuardMap.abstractionErrorCora` is the
zonotope `{0}`: center and every generator `0`. -/
theorem GuardMap.abstractionErrorCora_eq_zero (A : Mat ℝ n n) (x₀ : Vec ℝ n) (th tmax : ℝ)
    {η : ℕ} (hA : A ^ η = 0) (hW : MatExp.expRemainderMat A tmax η = 0) : -- --- CONCL ---
    (GuardMap.abstractionErrorCora A (Zonotope.ofPoint 0) (Zonotope.ofPoint x₀) th tmax η).c = 0
      ∧ ∀ j, (GuardMap.abstractionErrorCora A (Zonotope.ofPoint 0) (Zonotope.ofPoint x₀) th
        tmax η).G j = 0 := by -- --- PROOF ---
  have hW0 : (fun j k => |MatExp.expRemainderMat A tmax η j k| : Mat ℝ n n) = 0 := by
    ext j k; simp [hW]
  -- `err1`: `{0}` when the loop is not entered, else its last summand `(Aᵑ/η!)(...)`
  have h1 : ∀ (g : ℕ → Zonotope (Vec ℝ n)), (∀ m, m + 2 = η → aux_absErrCora_Zero (g m)) →
      aux_absErrCora_Zero ((List.range (η - 1)).foldl (fun _ m => g m)
        (Zonotope.ofPoint 0)) := by
    intro g hg
    obtain h | ⟨k, hk⟩ : η - 1 = 0 ∨ ∃ k, η - 1 = k + 1 :=
      (Nat.eq_zero_or_eq_succ_pred _).imp id fun h => ⟨_, h⟩
    · rw [h]; exact aux_absErrCora_ofPoint
    · rw [hk, aux_absErrCora_foldl]; exact hg k (by omega)
  -- the sets of `aux_abstractionError`, each `{0}`: no inputs, `W = 0`
  show aux_absErrCora_Zero _
  dsimp only [GuardMap.abstractionErrorCora]
  refine aux_absErrCora_plus (aux_absErrCora_plus (aux_absErrCora_mtimesIM _
    (aux_absErrCora_plus (aux_absErrCora_plus (h1 _ fun m hm => ?_)
      (aux_absErrCora_sumTerms (fun _ => aux_absErrCora_mtimesIM _ aux_absErrCora_ofPoint) η))
      (aux_absErrCora_plus (aux_absErrCora_recenter aux_absErrCora_ofPoint)
        (aux_absErrCora_sumTerms (fun _ => aux_absErrCora_mtimesIM _
          (aux_absErrCora_recenter aux_absErrCora_ofPoint)) η))))
    (aux_absErrCora_mtimesIM_zero ((congrArg Neg.neg hW0).trans neg_zero) hW0 _))
    (aux_absErrCora_mtimesIM _ aux_absErrCora_ofPoint)
  rw [hm, hA, smul_zero]
  exact aux_absErrCora_mtimes_zero _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
