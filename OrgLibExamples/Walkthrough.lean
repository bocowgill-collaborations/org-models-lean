import OrgLibExamples.ThreeComponent
import OrgLibExamples.Indexed
import OrgLibExamples.SharedCyclic

/-!
# Three demonstrations of one canonical NK evaluator

The worked three-component example, an ordered-neighbor application, and a shared
cyclic restriction all use canonical fitness. Source citations are in their example
modules. The last results distinguish continuous laws at the same fixed topology;
no statement here formalizes the papers' complete organizational dynamics.
-/

namespace OrgLibExamples.Walkthrough

open OrgLib.NK OrgLib.NK.SharedCyclic
open OrgLibExamples.SharedCyclic
open scoped BigOperators

/-- Preserve the leading zeros of the worked configuration `001`. -/
def threeComponentState : Config 3 := decode 1

/-- The worked example is an exact rational equality about the canonical evaluator. -/
theorem threeComponent_value : ThreeComponent.evaluate threeComponentState = 1 / 2 :=
  ThreeComponent.expected_code_1

/-- An application constructs canonical topology from explicit ordered neighbors. -/
def orderedTopology : Topology 3 2 :=
  Topology.ofNeighbors (by decide) Indexed.sortedNeighbors Indexed.sortedNeighbors_nonfocal

/-- Exact correspondence with the address-indexed average precedes inherited results. -/
theorem indexed_evaluator_correspondence (x : Config 3) :
    fitness orderedTopology (tablesFromEntries Indexed.entries) x =
      ∑ i, Indexed.entries i
        (encode (Fin.cases (x i) (fun j ↦ x (Indexed.sortedNeighbors i j)))) / 3 :=
  fitness_eq_indexedAverage (by decide) Indexed.sortedNeighbors
    Indexed.sortedNeighbors_nonfocal Indexed.entries x

/-- The application inherits the canonical bounds theorem under explicit entry bounds. -/
theorem indexed_inherits_bounds (x : Config 3) :
    fitness orderedTopology (tablesFromEntries Indexed.entries) x ∈ Set.Icc (0 : ℚ) 1 :=
  indexed_fitness_mem_Icc (by decide) Indexed.sortedNeighbors
    Indexed.sortedNeighbors_nonfocal Indexed.entries Indexed.entries_bounded x

/-- Sharing one cyclic table forces an additional rotation symmetry. -/
theorem shared_rotation (x : Config 3) (r : Fin 3) :
    sharedCyclic (by decide : 1 < 3) pairTable (rotate r x) =
      sharedCyclic (by decide) pairTable x :=
  sharedCyclic_fitness_rotate (by decide) pairTable x r

/-- A bounded canonical landscape separates the fixed labeled states `01` and `10`. -/
theorem counterexample_values :
    locusSpecificCyclic (by decide : 0 < 2) witnessTables state01 = 1 ∧
      locusSpecificCyclic (by decide : 0 < 2) witnessTables state10 = 0 :=
  ⟨witness_fitness_state01, witness_fitness_state10⟩

theorem counterexample_bounded : ∀ i w, witnessTables i w ∈ Set.Icc (0 : ℚ) 1 :=
  witnessTables_bounded

/-- This landscape has no shared rational-table representation at the same labeled states. -/
theorem no_shared_representation :
    ¬∃ φ : LocalWord 0 → ℚ, ∀ x,
      sharedCyclic (by decide : 0 < 2) φ x =
        locusSpecificCyclic (by decide : 0 < 2) witnessTables x :=
  witness_no_shared_representation

/-- Every shared cyclic landscape remains a deterministic canonical NK instance. -/
theorem shared_in_locus_specific {N K : ℕ} (hKN : K < N) (φ : LocalWord K → ℚ) :
    locusSpecificCyclic hKN (sharedTables φ) = sharedCyclic hKN φ :=
  locusSpecificCyclic_sharedTables hKN φ

/-- A sufficient continuous event has independent probability at least one sixteenth. -/
theorem independent_event_bound : (1 / 16 : ENNReal) ≤
    independentUniformCyclic (by decide : 0 < 2) (landscapeEvent state01 state10) :=
  independent_event_state01_state10

/-- Sharing the cyclic table gives that event exactly zero probability. -/
theorem shared_event_probability :
    sharedUniformCyclic (by decide : 0 < 2) (landscapeEvent state01 state10) = 0 :=
  shared_event_state01_state10

theorem continuous_laws_differ :
    sharedUniformCyclic (by decide : 0 < 2) ≠ independentUniformCyclic (by decide : 0 < 2) :=
  shared_independent_laws_ne

/-- At twelve loci and five interactions, the sufficient-event bound is still positive. -/
theorem twelve_locus_bound : (1 / 2 : ENNReal) ^ 24 ≤
    independentUniformCyclic (by decide : 5 < 12)
      (landscapeEvent alternating01 alternating10) :=
  independent_event_lower_bound_N12 (by decide)

theorem twelve_locus_laws_differ :
    sharedUniformCyclic (by decide : 5 < 12) ≠ independentUniformCyclic (by decide : 5 < 12) :=
  landscape_laws_ne_N12 (by decide)

/-- Five exact values used by the short newcomer executable. -/
def values : List ℚ :=
  [ThreeComponent.evaluate threeComponentState,
   fitness orderedTopology (tablesFromEntries Indexed.entries) Indexed.state,
   sharedCyclic (by decide : 1 < 3) pairTable singleLastBit,
   locusSpecificCyclic (by decide : 0 < 2) witnessTables state01,
   locusSpecificCyclic (by decide : 0 < 2) witnessTables state10]

/-- info: [1 / 2, 13 / 63, 5 / 27, 1, 0] -/
#guard_msgs in
#eval values

end OrgLibExamples.Walkthrough
