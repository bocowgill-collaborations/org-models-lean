import OrgLib

/-!
# Exact rational-to-real public interpretation

The cast theorem covers every canonical topology and arbitrary rational table values.
The adapter applications use the same table interpretation and evaluator.
-/

namespace OrgLibTest.Cast

open OrgLib.NK
open OrgLib.NK.SharedCyclic

variable {N K : ℕ}

example (T : Topology N K) (c : Tables N K ℚ) (x : Config N) :
    ((fitness T c x : ℚ) : ℝ) = fitness T (fun i w ↦ (c i w : ℝ)) x :=
  fitness_ratCast T c x

example (T : Topology N K) (c : Tables N K ℚ) (x : Config N) (i : Fin N) :
    ((contribution T c x i : ℚ) : ℝ) = contribution T (fun j w ↦ (c j w : ℝ)) x i :=
  contribution_ratCast T c x i

example (hKN : K < N) (neighbors : Fin N → (Fin K ↪ Fin N))
    (hne : ∀ i j, neighbors i j ≠ i) (entries : TableEntries N K ℚ) (x : Config N) :
    ((fitness (OrgLib.NK.Topology.ofNeighbors hKN neighbors hne)
      (tablesFromEntries entries) x : ℚ) : ℝ) =
      fitness (OrgLib.NK.Topology.ofNeighbors hKN neighbors hne)
        (tablesFromEntries (fun i q ↦ (entries i q : ℝ))) x :=
  fitness_ratCast (OrgLib.NK.Topology.ofNeighbors hKN neighbors hne)
    (tablesFromEntries entries) x

example (hKN : K < N) (φ : LocalWord K → ℚ) (x : Config N) :
    ((sharedCyclic hKN φ x : ℚ) : ℝ) = sharedCyclic hKN (fun w ↦ (φ w : ℝ)) x :=
  fitness_ratCast (cyclicTopology hKN) (sharedTables φ) x

example (hKN : K < N) (c : Tables N K ℚ) (x : Config N) :
    ((locusSpecificCyclic hKN c x : ℚ) : ℝ) =
      locusSpecificCyclic hKN (fun i w ↦ (c i w : ℝ)) x :=
  fitness_ratCast (cyclicTopology hKN) c x

end OrgLibTest.Cast
