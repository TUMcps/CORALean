module

public import CORALean.ContSet.ContSet.Definitions.Interfaces
public import Mathlib.Topology.MetricSpace.HausdorffDistance

@[expose] public section

/-!
# Adding a set to both sides cannot move them apart

[1, Lemma 1]: `d_H(S ⊕ V, S ⊕ W) ≤ d_H(V, W)`. Translating both sets by the same `s` leaves their
distance alone, so the summand `S` adds nothing. That lets order reduction be analyzed on the part
actually reduced: `d_H(Z_full, Z_red)` is `d_H(Z' ⊕ Z, Z' ⊕ box(Z))`, bounded by `d_H(Z, box(Z))`.
Stated on plain sets and the *exact* Minkowski sum, not `Plus.plus`, which only encloses. `V` and
`W` are compact and nonempty; Mathlib's `hausdorffDist` is `0` wherever `hausdorffEDist` is `⊤`, so
without those two the statement would be about that junk value. An empty `S` makes both sums empty
and the bound reads `0 ≤ d_H(V, W)`.

## Inputs
* `S` – set
* `V` – set
* `W` – set

## Hypotheses
* `hV` – `V` compact
* `hVne` – `V` nonempty
* `hW` – `W` compact
* `hWne` – `W` nonempty

## Conclusion
* distance of `S + V` and `S + W` is at most that of `V` and `W`

## References

* [1] [M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive Reachability Algorithms
      for Nonlinear Systems Using Abstraction Error Analysis". Nonlinear Analysis: Hybrid Systems,
      2022.](../../../../../references/2022/wetzlinger-nahs-abstraction-error.md)
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise

variable {α : Type} [NormedAddCommGroup α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One direction: a point of `S + V` has a point of `S + W` within `d_H(V, W)`
of it, the summand from `S` kept and only the other one moved. -/
private theorem aux_exists_mem_add_dist_le {S V W : Set α} (hW : IsCompact W) (hWne : W.Nonempty)
    (hfin : Metric.hausdorffEDist V W ≠ ⊤) {x : α} (hx : x ∈ S + V) : -- --- CONCL ---
    ∃ y ∈ S + W, dist x y ≤ Metric.hausdorffDist V W := by -- --- PROOF ---
  obtain ⟨s, hs, v, hv, rfl⟩ := Set.mem_add.mp hx
  obtain ⟨w, hw, hvw⟩ := hW.exists_infDist_eq_dist hWne v
  refine ⟨s + w, Set.add_mem_add hs hw, ?_⟩
  rw [dist_add_left, ← hvw]
  exact Metric.infDist_le_hausdorffDist_of_mem hv hfin


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 1]: the same set added to both sides can only bring them
together. -/
theorem hausdorffDist_add_le {S V W : Set α} (hV : IsCompact V) (hVne : V.Nonempty)
    (hW : IsCompact W) (hWne : W.Nonempty) : -- --- CONCL ---
    Metric.hausdorffDist (S + V) (S + W) ≤ Metric.hausdorffDist V W := by -- --- PROOF ---
  have hfin : Metric.hausdorffEDist V W ≠ ⊤ :=
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded hVne hWne hV.isBounded hW.isBounded
  refine Metric.hausdorffDist_le_of_mem_dist Metric.hausdorffDist_nonneg
    (fun _ hx => aux_exists_mem_add_dist_le hW hWne hfin hx) ?_
  -- the other side is the same statement with `V` and `W` exchanged
  intro x hx
  obtain ⟨y, hy, hxy⟩ :=
    aux_exists_mem_add_dist_le hV hVne (by rwa [Metric.hausdorffEDist_comm]) hx
  exact ⟨y, hy, by rwa [Metric.hausdorffDist_comm] at hxy⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
