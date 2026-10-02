import CORALean.ContSet.ContSet.Definitions.CompactSet
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Adding a set to both sides cannot move them apart

[1, Lemma 1]: `d_H(S ⊕ V, S ⊕ W) ≤ d_H(V, W)`. Translating both sets by the
same `s` leaves the distance between them alone, so the summand `S` adds
nothing to it. That is what lets order reduction be analyzed on the part that
is actually reduced: `d_H(Z_full, Z_red)` is `d_H(Z' ⊕ Z, Z' ⊕ box(Z))`, which
this bounds by `d_H(Z, box(Z))`.

Stated on plain sets and on the *exact* Minkowski sum — `+` under `Pointwise`,
not `Plus.plus`, which only encloses and so carries no distance bound at all.

`V` and `W` are compact and nonempty; `S` is anything. Mathlib's
`hausdorffDist` is a real number that is `0` wherever `hausdorffEDist` is `⊤`,
so without those two the statement would be about that junk value on the sets
where it is one. `CompactSet` discharges compactness at every
representation here, and a centre or a vertex the nonemptiness. An empty `S`
makes both sums empty and the bound reads `0 ≤ d_H(V, W)`, which holds.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive Reachability
      Algorithms for Nonlinear Systems Using Abstraction Error Analysis". Nonlinear
      Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Tobias Ladner
-- Written:       13-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise

variable {α : Type} [NormedAddCommGroup α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One direction: a point of `S + V` has a point of `S + W` within `d_H(V, W)`
of it, the summand from `S` kept and only the other one moved. -/
theorem aux_exists_mem_add_dist_le {S V W : Set α} (hW : IsCompact W) (hWne : W.Nonempty)
    (hfin : Metric.hausdorffEDist V W ≠ ⊤) {x : α} (hx : x ∈ S + V) :
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
    (hW : IsCompact W) (hWne : W.Nonempty) :
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
