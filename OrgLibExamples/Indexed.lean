import OrgLib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Embedding
import Mathlib.Tactic.NormNum

/-!
# Ordered-neighborhood NK examples

The quality component of Ganz, *Conflict, Chaos, and the Art of Institutional Design*,
§3.1 (DOI 10.1287/orsc.2023.1662), uses this canonical construction.

These rational fixtures are defined directly in Lean, independently of R. The first
uses increasing nonfocal neighbors, as in the source generator's sorted output. The
second deliberately reverses those supplied neighbors: the adapter must retain that
order. Locus-specific tables make the resulting change in fitness observable.

These checks establish exact Lean fixture values. Cross-language numerical validation
and correctness of the original source sampler are separate questions.
-/

namespace OrgLibExamples.Indexed

open OrgLib.NK

/-- Increasing neighbors obtained by omitting the focal coordinate. -/
def sortedNeighbors (i : Fin 3) : Fin 2 ↪ Fin 3 := i.succAboveEmb

/-- Every supplied neighbor differs from its focal coordinate. -/
theorem sortedNeighbors_nonfocal (i : Fin 3) (j : Fin 2) : sortedNeighbors i j ≠ i :=
  Fin.succAbove_ne i j

/-- This fixture has the increasing order produced by the source generator's sort. -/
theorem sortedNeighbors_increasing : ∀ i, StrictMono (sortedNeighbors i) := by
  decide

/-- A valid supplied order that is deliberately decreasing rather than sorted. -/
def reversedNeighbors (i : Fin 3) : Fin 2 ↪ Fin 3 :=
  (Equiv.swap 0 1).toEmbedding.trans (sortedNeighbors i)

/-- Reordering these neighbors preserves their exclusion of the focal coordinate. -/
theorem reversedNeighbors_nonfocal (i : Fin 3) (j : Fin 2) : reversedNeighbors i j ≠ i :=
  sortedNeighbors_nonfocal i (Equiv.swap 0 1 j)

/-- Distinct locus weights preserve table boundedness while exposing input ordering. -/
def entries : TableEntries 3 2 ℚ := fun i q ↦ (q.val : ℚ) * (i.val + 1) / 21

/-- A state with the middle bit true and both boundary bits false. -/
def state : Config 3 := fun i ↦ i == 1

/-- The source-shaped sorted-neighbor interpretation at maximal arity. -/
def sortedTopology : Topology 3 2 :=
  Topology.ofNeighbors (by decide) sortedNeighbors sortedNeighbors_nonfocal

/-- A second valid interpretation preserves the supplied reversed-neighbor order. -/
def reversedTopology : Topology 3 2 :=
  Topology.ofNeighbors (by decide) reversedNeighbors reversedNeighbors_nonfocal

/-- Every entry satisfies the hypothesis required to inherit canonical fitness bounds. -/
theorem entries_bounded : ∀ i q, entries i q ∈ Set.Icc (0 : ℚ) 1 := by
  change ∀ (i : Fin 3) (q : Fin 8), entries i q ∈ Set.Icc (0 : ℚ) 1
  norm_num [Fin.forall_fin_succ, entries]

/-- The adapter inherits canonical bounds for every configuration of this fixture. -/
theorem sorted_bounded (x : Config 3) :
    fitness sortedTopology (tablesFromEntries entries) x ∈ Set.Icc (0 : ℚ) 1 :=
  indexed_fitness_mem_Icc (by decide) sortedNeighbors sortedNeighbors_nonfocal
    entries entries_bounded x

/-- The first reversed neighborhood really is the unsorted sequence 2,1. -/
theorem reversedNeighbors_at_zero : reversedNeighbors 0 0 = 2 ∧ reversedNeighbors 0 1 = 1 := by
  decide

/-- Supplied neighbor order becomes local-word order without an intervening sort. -/
theorem reversed_word_at_zero :
    List.ofFn (extract reversedTopology state 0) = [false, false, true] := by
  decide

/-- No nonfocal inputs are needed when K=0. -/
def noNeighbors (_ : Fin 2) : Fin 0 ↪ Fin 2 := Function.Embedding.ofIsEmpty

/-- The empty neighbor sequence vacuously excludes the focal coordinate. -/
theorem noNeighbors_nonfocal (i : Fin 2) (j : Fin 0) : noNeighbors i j ≠ i :=
  Fin.elim0 j

/-- A separable adapter instance with two loci. -/
def zeroTopology : Topology 2 0 := Topology.ofNeighbors (by decide) noNeighbors noNeighbors_nonfocal

/-- The loci gain one and one half, respectively, from choosing true. -/
def zeroEntries : TableEntries 2 0 ℚ :=
  fun i q ↦ if i = 0 then (q.val : ℚ) else q.val / 2

/-- Both loci choose their preferred bit. -/
def best : Config 2 := fun _ ↦ true

/-- Exact evaluation of the separable adapter instance. -/
theorem best_fitness : fitness zeroTopology (tablesFromEntries zeroEntries) best = 3 / 4 := by
  norm_num [fitness_K_zero, tablesFromEntries, zeroEntries, best, Fin.sum_univ_succ,
    show encode (fun _ : Fin 1 ↦ true) = 1 by decide]

/-- Neither one-bit flip improves the two-locus candidate. -/
theorem best_local :
    IsOneBitLocalMax (fitness zeroTopology (tablesFromEntries zeroEntries)) best := by
  norm_num [IsOneBitLocalMax, Fin.forall_fin_succ, fitness_K_zero, tablesFromEntries,
    zeroEntries, best, OrgLib.NK.flip, Function.update, Fin.sum_univ_succ,
    show encode (fun _ : Fin 1 ↦ true) = 1 by decide,
    show encode (fun _ : Fin 1 ↦ false) = 0 by decide]

/-- The canonical zero-interaction theorem proves global maximality from a local check. -/
theorem best_global :
    IsMaxOn (fitness zeroTopology (tablesFromEntries zeroEntries)) Set.univ best :=
  (indexed_isOneBitLocalMax_iff_isMaxOn_K_zero (by decide)
    noNeighbors noNeighbors_nonfocal zeroEntries best).mp best_local

/--
info: [13 / 63, 5 / 21]
-/
#guard_msgs in
#eval [fitness sortedTopology (tablesFromEntries entries) state,
  fitness reversedTopology (tablesFromEntries entries) state]

/--
info: [2, 4, 1]
-/
#guard_msgs in
#eval List.ofFn (fun i : Fin 3 ↦ (encode (extract sortedTopology state i)).val)

/--
info: [1, 4, 2]
-/
#guard_msgs in
#eval List.ofFn (fun i : Fin 3 ↦ (encode (extract reversedTopology state i)).val)

end OrgLibExamples.Indexed
