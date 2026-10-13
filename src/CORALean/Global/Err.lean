module

public import CORALean.Global.BoxDiameter
public import CORALean.Global.EuclideanNorm
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice

@[expose] public section

/-!
# `err(S) := rad(box(S))`, the Euclidean radius of the smallest ball at the origin enclosing `S`

[1]'s eq. (11): `err(S) := rad(box(S))`, with `rad` "the radius of the smallest hypersphere
centered at the origin and enclosing a set" and `box(S)` "the tightest axis-aligned interval
outer-approximation of `S`" (Sec. II-A, Notation) — a *hypersphere* is Euclidean by construction,
matching [1, Def. 5]'s own `‖·‖₂` for the Hausdorff distance `err` bounds via eq. (12). This is the
ORIGIN-centred reading, not `Interval.radius`'s own-centre one (which would instead be
`‖boxDiameter S / 2‖₂` and gives a different number whenever `box(S)` is not centred at `0`):
`box(S)`'s farthest corner has magnitude `max |inf_i S| |sup_i S|` per coordinate, matching CDC'20
`Prop. 1`'s `hausdorffDist₂_add_le_box_radius`, already in this tree, read off a bare `Set` rather
than a fixed `Interval`.

`err_le_sqrt_mul_norm_boxDiameter` and `norm_boxDiameter_le_two_mul_err` bridge `err` to
`boxDiameter`'s own, more developed `add_le`/`mulVec_image_le` bounds, so a caller with `0 ∈ S` (the
case every error term of [1] is in) gets `err`'s behaviour on a sum or a linear image at a loose but
sound constant, rather than a second proof of the same `sSup`/`sInf` sandwiching.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Opus 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point between two endpoints never exceeds the max of their magnitudes. -/
theorem aux_err_abs_between {lo x hi : ℝ} (h1 : lo ≤ x) (h2 : x ≤ hi) : |x| ≤ max |lo| |hi| :=
  abs_le.mpr ⟨by linarith [neg_abs_le lo, neg_le_neg (le_max_left |lo| |hi|)],
    h2.trans ((le_abs_self hi).trans (le_max_right _ _))⟩

/-- Squaring is monotone on magnitudes, so a coordinatewise bound on magnitudes is a bound on the
Euclidean norm. -/
theorem aux_err_norm₂_le_of_abs_le {x y : Vec ℝ n} (h : ∀ i, |x i| ≤ |y i|) : ‖x‖₂ ≤ ‖y‖₂ := by
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  have hi := mul_self_le_mul_self (abs_nonneg (x i)) (h i)
  rwa [abs_mul_abs_self, abs_mul_abs_self, ← pow_two, ← pow_two] at hi


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1]'s eq. (11): `err(S) := rad(box(S))`, the Euclidean radius at the origin of the tightest
axis-aligned box over `S` — its farthest corner, read coordinatewise. -/
noncomputable def err (S : Set (Vec ℝ n)) : ℝ :=
  ‖fun i => max |sSup ((fun x : Vec ℝ n => x i) '' S)| |sInf ((fun x : Vec ℝ n => x i) '' S)|‖₂

theorem err_nonneg (S : Set (Vec ℝ n)) : 0 ≤ err S := norm₂_nonneg _

/-- A larger set has a no-smaller `err`, provided the larger one is bounded at all and the smaller
one is not empty — [1]'s own use of `err` is always monotone in exactly this shape. -/
theorem err_mono {S T : Set (Vec ℝ n)} (hne : S.Nonempty) (hT : Bornology.IsBounded T)
    (hST : S ⊆ T) : err S ≤ err T := by -- --- PROOF ---
  refine aux_err_norm₂_le_of_abs_le fun i => ?_
  set imS := (fun x : Vec ℝ n => x i) '' S
  set imT := (fun x : Vec ℝ n => x i) '' T
  have himg : imS ⊆ imT := Set.image_mono hST
  have hneS : imS.Nonempty := hne.image _
  have hbAT : BddAbove imT := bddAbove_eval_image hT i
  have hbBT : BddBelow imT := bddBelow_eval_image hT i
  have hbAS : BddAbove imS := hbAT.mono himg
  have hbBS : BddBelow imS := hbBT.mono himg
  have hInfSup : sInf imS ≤ sSup imS := csInf_le_csSup hneS hbBS hbAS
  -- both endpoints of `S`'s box lie between `T`'s, so both are dominated in magnitude
  have hSup : |sSup imS| ≤ max |sSup imT| |sInf imT| := by
    rw [max_comm]
    exact aux_err_abs_between ((csInf_le_csInf hbBT hneS himg).trans hInfSup)
      (csSup_le_csSup hbAT hneS himg)
  have hInf : |sInf imS| ≤ max |sSup imT| |sInf imT| := by
    rw [max_comm]
    exact aux_err_abs_between (csInf_le_csInf hbBT hneS himg)
      (hInfSup.trans (csSup_le_csSup hbAT hneS himg))
  calc |(max |sSup imS| |sInf imS|)|
      = max |sSup imS| |sInf imS| := abs_of_nonneg (le_max_of_le_left (abs_nonneg _))
    _ ≤ max |sSup imT| |sInf imT| := max_le hSup hInf
    _ = |(max |sSup imT| |sInf imT|)| := (abs_of_nonneg (le_max_of_le_left (abs_nonneg _))).symm

/-- Every member of a bounded set is within `err`'s reach of the origin — [1]'s eq. (12),
`d_H(0,S) ≤ err(S)`, read off a single witness rather than the Hausdorff distance. -/
theorem norm₂_le_err_of_mem {S : Set (Vec ℝ n)} (hS : Bornology.IsBounded S) {x : Vec ℝ n}
    (hx : x ∈ S) : ‖x‖₂ ≤ err S := by -- --- PROOF ---
  refine aux_err_norm₂_le_of_abs_le fun i => ?_
  have h1 : sInf ((fun z : Vec ℝ n => z i) '' S) ≤ x i :=
    csInf_le (bddBelow_eval_image hS i) ⟨x, hx, rfl⟩
  have h2 : x i ≤ sSup ((fun z : Vec ℝ n => z i) '' S) :=
    le_csSup (bddAbove_eval_image hS i) ⟨x, hx, rfl⟩
  calc |x i|
      ≤ max |sInf ((fun z : Vec ℝ n => z i) '' S)| |sSup ((fun z : Vec ℝ n => z i) '' S)| :=
        aux_err_abs_between h1 h2
    _ = max |sSup ((fun z : Vec ℝ n => z i) '' S)| |sInf ((fun z : Vec ℝ n => z i) '' S)| :=
        max_comm _ _
    _ ≤ |(max |sSup ((fun z : Vec ℝ n => z i) '' S)| |sInf ((fun z : Vec ℝ n => z i) '' S)|)| :=
        le_abs_self _

/-- `err` of a Minkowski sum is at most the sum of `err`'s — the triangle inequality [1, Lemma
2]'s Appendix B proof takes for granted while combining a step's error terms. -/
theorem err_add_le {S T : Set (Vec ℝ n)} (hSne : S.Nonempty) (hTne : T.Nonempty)
    (hS : Bornology.IsBounded S) (hT : Bornology.IsBounded T) :
    err (S + T) ≤ err S + err T := by -- --- PROOF ---
  have himg : ∀ i : Fin n, (fun x : Vec ℝ n => x i) '' (S + T)
      = (fun x : Vec ℝ n => x i) '' S + (fun x : Vec ℝ n => x i) '' T := by
    intro i; ext y
    simp only [Set.mem_image, Set.mem_add]
    constructor
    · rintro ⟨x, ⟨s, hs, t, ht, rfl⟩, rfl⟩
      exact ⟨s i, ⟨s, hs, rfl⟩, t i, ⟨t, ht, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨s, hs, rfl⟩, _, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨s + t, ⟨s, hs, t, ht, rfl⟩, rfl⟩
  have hcoord : ∀ i : Fin n,
      |(max |sSup ((fun x : Vec ℝ n => x i) '' (S + T))|
        |sInf ((fun x : Vec ℝ n => x i) '' (S + T))|)|
        ≤ |(max |sSup ((fun x : Vec ℝ n => x i) '' S)| |sInf ((fun x : Vec ℝ n => x i) '' S)|
            + max |sSup ((fun x : Vec ℝ n => x i) '' T)|
              |sInf ((fun x : Vec ℝ n => x i) '' T)|)| := by
    -- read `(S + T)`'s box corner off `S`'s and `T`'s own `sSup`/`sInf`, which add
    intro i
    have hSA := bddAbove_eval_image hS i
    have hSB := bddBelow_eval_image hS i
    have hTA := bddAbove_eval_image hT i
    have hTB := bddBelow_eval_image hT i
    have hSne' : ((fun x : Vec ℝ n => x i) '' S).Nonempty := hSne.image _
    have hTne' : ((fun x : Vec ℝ n => x i) '' T).Nonempty := hTne.image _
    rw [himg, csSup_add hSne' hSA hTne' hTA, csInf_add hSne' hSB hTne' hTB]
    set a := sSup ((fun x : Vec ℝ n => x i) '' S)
    set b := sInf ((fun x : Vec ℝ n => x i) '' S)
    set c := sSup ((fun x : Vec ℝ n => x i) '' T)
    set d := sInf ((fun x : Vec ℝ n => x i) '' T)
    have hac : (0:ℝ) ≤ max |a| |b| + max |c| |d| :=
      add_nonneg (le_max_of_le_left (abs_nonneg a)) (le_max_of_le_left (abs_nonneg c))
    rw [abs_of_nonneg (le_max_of_le_left (abs_nonneg (a + c))), abs_of_nonneg hac]
    -- the triangle inequality on each endpoint, then each side picks its own `max` term
    refine max_le ?_ ?_
    · exact (abs_add_le a c).trans (add_le_add (le_max_left |a| |b|) (le_max_left |c| |d|))
    · exact (abs_add_le b d).trans (add_le_add (le_max_right |a| |b|) (le_max_right |c| |d|))
  calc err (S + T) ≤ ‖fun i => max |sSup ((fun x : Vec ℝ n => x i) '' S)|
        |sInf ((fun x : Vec ℝ n => x i) '' S)|
        + max |sSup ((fun x : Vec ℝ n => x i) '' T)| |sInf ((fun x : Vec ℝ n => x i) '' T)|‖₂ :=
        aux_err_norm₂_le_of_abs_le hcoord
    _ ≤ err S + err T := norm₂_add_le _ _

/-- `err` scales with a non-negative factor: the box of `c • S` is `c` times `S`'s, both
endpoints scaling with it, and so is its farthest corner — what a superlinear-decrease argument
uses to take a factor `φ` out of an error term. -/
theorem err_smul_of_nonneg {c : ℝ} (hc : 0 ≤ c) (S : Set (Vec ℝ n)) :
    err (c • S) = c * err S := by -- --- PROOF ---
  have himg : ∀ i : Fin n, (fun x : Vec ℝ n => x i) '' (c • S)
      = c • ((fun x : Vec ℝ n => x i) '' S) := by
    intro i
    rw [← Set.image_smul, ← Set.image_smul, Set.image_image, Set.image_image]
    rfl
  -- each coordinate's endpoints scale by `c`, and so does the larger of their magnitudes
  have hvec : (fun i => max |sSup ((fun x : Vec ℝ n => x i) '' (c • S))|
        |sInf ((fun x : Vec ℝ n => x i) '' (c • S))|)
      = c • fun i => max |sSup ((fun x : Vec ℝ n => x i) '' S)|
        |sInf ((fun x : Vec ℝ n => x i) '' S)| := by
    funext i
    rw [himg, Real.sSup_smul_of_nonneg hc, Real.sInf_smul_of_nonneg hc, Pi.smul_apply,
      smul_eq_mul, smul_eq_mul, smul_eq_mul, abs_mul, abs_mul, abs_of_nonneg hc,
      mul_max_of_nonneg _ _ hc]
  rw [err, hvec, norm₂_smul, abs_of_nonneg hc, err]

/-- `boxDiameter`'s own width is at most twice `err`'s reach, the two endpoints' magnitudes each
bounding it. -/
theorem norm_boxDiameter_le_two_mul_err (S : Set (Vec ℝ n)) (hSne : S.Nonempty)
    (hS : Bornology.IsBounded S) : ‖boxDiameter S‖ ≤ 2 * err S := by -- --- PROOF ---
  refine pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) (err_nonneg S)) |>.mpr fun i => ?_
  have hbd : boxDiameter S i
      = sSup ((fun x : Vec ℝ n => x i) '' S) - sInf ((fun x : Vec ℝ n => x i) '' S) := rfl
  have hle : boxDiameter S i ≤ 2 *
      max |sSup ((fun x : Vec ℝ n => x i) '' S)| |sInf ((fun x : Vec ℝ n => x i) '' S)| := by
    -- split the width `sSup - sInf` into its two endpoints, each under the box corner
    rw [hbd, two_mul]
    have h1 : sSup ((fun x : Vec ℝ n => x i) '' S)
        ≤ max |sSup ((fun x : Vec ℝ n => x i) '' S)| |sInf ((fun x : Vec ℝ n => x i) '' S)| :=
      (le_abs_self _).trans (le_max_left _ _)
    have h2 : -sInf ((fun x : Vec ℝ n => x i) '' S)
        ≤ max |sSup ((fun x : Vec ℝ n => x i) '' S)| |sInf ((fun x : Vec ℝ n => x i) '' S)| :=
      (neg_le_abs _).trans (le_max_right _ _)
    linarith
  have hnn : 0 ≤ boxDiameter S i := by
    have h : sInf ((fun x : Vec ℝ n => x i) '' S) ≤ sSup ((fun x : Vec ℝ n => x i) '' S) :=
      csInf_le_csSup (hSne.image _) (bddBelow_eval_image hS i) (bddAbove_eval_image hS i)
    rw [hbd]; linarith
  -- the box corner at `i` is one coordinate of `err`'s own vector, so `abs_le_norm₂` reaches it
  have hmaxle : max |sSup ((fun x : Vec ℝ n => x i) '' S)| |sInf ((fun x : Vec ℝ n => x i) '' S)|
      ≤ err S := by
    have h := abs_le_norm₂ (fun i => max |sSup ((fun x : Vec ℝ n => x i) '' S)|
      |sInf ((fun x : Vec ℝ n => x i) '' S)|) i
    rwa [abs_of_nonneg (le_max_of_le_left (abs_nonneg _))] at h
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact hle.trans (mul_le_mul_of_nonneg_left hmaxle (by norm_num))

/-- `err`, read off `boxDiameter` when `0` is in the set — the case every error term of [1] is in,
since it always encloses `0`. Loose by a factor `√n` against the tight `err` bound: `boxDiameter`
reads the box's own extent in the supremum norm, `err` in the Euclidean one. -/
theorem err_le_sqrt_mul_norm_boxDiameter {S : Set (Vec ℝ n)} (h0 : (0 : Vec ℝ n) ∈ S)
    (hS : Bornology.IsBounded S) : err S ≤ Real.sqrt n * ‖boxDiameter S‖ := by -- --- PROOF ---
  have hcoord : ∀ i : Fin n,
      max |sSup ((fun x : Vec ℝ n => x i) '' S)| |sInf ((fun x : Vec ℝ n => x i) '' S)|
        ≤ ‖boxDiameter S‖ := by
    intro i
    have hsup0 : (0:ℝ) ≤ sSup ((fun x : Vec ℝ n => x i) '' S) := by
      simpa using le_csSup (bddAbove_eval_image hS i)
        (Set.mem_image_of_mem (fun x : Vec ℝ n => x i) h0)
    have hinf0 : sInf ((fun x : Vec ℝ n => x i) '' S) ≤ 0 := by
      simpa using csInf_le (bddBelow_eval_image hS i)
        (Set.mem_image_of_mem (fun x : Vec ℝ n => x i) h0)
    have hbd : boxDiameter S i
        = sSup ((fun x : Vec ℝ n => x i) '' S) - sInf ((fun x : Vec ℝ n => x i) '' S) := rfl
    -- `0` between the endpoints turns both magnitudes into the two halves of the width
    have hmax : max |sSup ((fun x : Vec ℝ n => x i) '' S)| |sInf ((fun x : Vec ℝ n => x i) '' S)|
        ≤ boxDiameter S i := by
      rw [hbd, abs_of_nonneg hsup0, abs_of_nonpos hinf0]
      exact max_le (by linarith) (by linarith)
    have hle : boxDiameter S i ≤ ‖boxDiameter S‖ :=
      (le_abs_self _).trans (norm_le_pi_norm (boxDiameter S) i |>.trans_eq' (Real.norm_eq_abs _))
    exact hmax.trans hle
  -- every coordinate of `err`'s vector is under the constant `‖boxDiameter S‖`, giving `√n` copies
  have hstep : err S ≤ ‖fun _ : Fin n => ‖boxDiameter S‖‖₂ :=
    aux_err_norm₂_le_of_abs_le fun i => (abs_of_nonneg (le_max_of_le_left (abs_nonneg _))
      |>.trans_le (hcoord i)).trans_eq (abs_of_nonneg (norm_nonneg _)).symm
  refine hstep.trans_eq ?_
  rw [norm₂]
  have : (∑ _i : Fin n, ‖boxDiameter S‖ ^ 2) = n * ‖boxDiameter S‖ ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
  rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

/-- If every point of `S` is within `r` of the origin, `err S` is within `√n · r` — the pointwise
route to a bound on `err`, avoiding a second `boxDiameter` computation. -/
theorem err_le_of_forall_norm₂_le {S : Set (Vec ℝ n)} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ y ∈ S, ‖y‖₂ ≤ r) : err S ≤ Real.sqrt n * r := by -- --- PROOF ---
  have hcoord : ∀ i : Fin n,
      max |sSup ((fun x : Vec ℝ n => x i) '' S)| |sInf ((fun x : Vec ℝ n => x i) '' S)| ≤ r := by
    intro i
    rcases Set.eq_empty_or_nonempty S with hS | ⟨y0, hy0⟩
    · simp [hS, Real.sSup_empty, Real.sInf_empty, hr]
    -- both endpoints of the box at `i` are themselves values of `S`-points at `i`, so `h` reaches
    have hA : ∀ z ∈ (fun x : Vec ℝ n => x i) '' S, z ≤ r := by
      rintro _ ⟨y, hy, rfl⟩; exact (le_abs_self _).trans ((abs_le_norm₂ y i).trans (h y hy))
    have hB : ∀ z ∈ (fun x : Vec ℝ n => x i) '' S, -r ≤ z := by
      rintro _ ⟨y, hy, rfl⟩
      exact (abs_le.mp ((abs_le_norm₂ y i).trans (h y hy))).1
    have hbA : BddAbove ((fun x : Vec ℝ n => x i) '' S) := ⟨r, hA⟩
    have hbB : BddBelow ((fun x : Vec ℝ n => x i) '' S) := ⟨-r, hB⟩
    have hmemi : y0 i ∈ (fun x : Vec ℝ n => x i) '' S := ⟨y0, hy0, rfl⟩
    have hsup_le : sSup ((fun x : Vec ℝ n => x i) '' S) ≤ r := csSup_le ⟨y0 i, hmemi⟩ hA
    have hsup_ge : -r ≤ sSup ((fun x : Vec ℝ n => x i) '' S) :=
      (hB (y0 i) hmemi).trans (le_csSup hbA hmemi)
    have hinf_ge : -r ≤ sInf ((fun x : Vec ℝ n => x i) '' S) := le_csInf ⟨y0 i, hmemi⟩ hB
    have hinf_le : sInf ((fun x : Vec ℝ n => x i) '' S) ≤ r :=
      (csInf_le hbB hmemi).trans (hA (y0 i) hmemi)
    exact max_le (abs_le.mpr ⟨hsup_ge, hsup_le⟩) (abs_le.mpr ⟨hinf_ge, hinf_le⟩)
  -- `err`'s vector is coordinatewise under the constant `r`, so its norm is under `√n · r`
  have hstep : err S ≤ ‖fun _ : Fin n => r‖₂ :=
    aux_err_norm₂_le_of_abs_le fun i => (abs_of_nonneg (le_max_of_le_left (abs_nonneg _))
      |>.trans_le (hcoord i)).trans_eq (abs_of_nonneg hr).symm
  refine hstep.trans_eq ?_
  rw [norm₂]
  have : (∑ _i : Fin n, r ^ 2) = n * r ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
  rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq hr]

/-- Applying a matrix scales `err` by at most `√n` times the sum of its rows' own Euclidean
norms — every point of `S` is within `err S` of the origin, and `norm₂_mulVec_le` carries that
through `M`. -/
theorem err_mulVec_le (M : Mat ℝ n n) {S : Set (Vec ℝ n)} (hS : Bornology.IsBounded S) :
    err (M.mulVec '' S) ≤ Real.sqrt n * (∑ i, ‖(fun j => M i j)‖₂) * err S := by -- --- PROOF ---
  have hr : (0:ℝ) ≤ (∑ i, ‖(fun j => M i j)‖₂) * err S :=
    mul_nonneg (Finset.sum_nonneg fun i _ => norm₂_nonneg _) (err_nonneg S)
  refine (err_le_of_forall_norm₂_le hr ?_).trans_eq (mul_assoc _ _ _).symm
  rintro _ ⟨x, hx, rfl⟩
  exact (norm₂_mulVec_le M x).trans (mul_le_mul_of_nonneg_left (norm₂_le_err_of_mem hS hx)
    (Finset.sum_nonneg fun i _ => norm₂_nonneg _))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
