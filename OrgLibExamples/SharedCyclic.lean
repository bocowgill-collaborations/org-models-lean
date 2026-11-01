import OrgLib
import Mathlib.Tactic.NormNum

/-!
# Exact examples of shared and locus-specific cyclic landscapes

The shared construction is the quality landscape in Ganz, *Adaptive Rationality,
Garbage Cans, and the Policy Process*, §2.2 (DOI 10.1108/S0733-558X20210000076004).

These fixtures exercise forward cyclic windows, wrapping, rotation, zero-interaction
Hamming counts, maxima with ties, and the fixed-label separation witness. The
examples are standalone Lean data. They make no stochastic or cross-language claim.
-/

namespace OrgLibExamples.SharedCyclic

open OrgLib.NK
open OrgLib.NK.SharedCyclic

/-- The state `001`, with slot zero the most significant bit. -/
def singleLastBit : Config 3 := fun i ↦ i == 2

/-- The state `010`, with the same number of true bits. -/
def singleMiddleBit : Config 3 := fun i ↦ i == 1

/-- An asymmetric bounded two-slot table with nonlinear address weights. -/
def pairEntries (q : Fin (2 ^ 2)) : ℚ := (q.val : ℚ) ^ 2 / 9

/-- Interpret that vector using the shared binary codec. -/
def pairTable (w : LocalWord 1) : ℚ := pairEntries (encode w)

/-- A maximal-arity three-slot table, still bounded by one. -/
def fullEntries (q : Fin (2 ^ 3)) : ℚ := (q.val : ℚ) ^ 2 / 49

/-- Interpret the three-slot vector as one shared contribution table. -/
def fullTable (w : LocalWord 2) : ℚ := fullEntries (encode w)

/-- At zero interactions, choosing true is strictly better at every locus. -/
def truePreferred (w : LocalWord 0) : ℚ := if w 0 then 3 / 4 else 1 / 4

/-- At zero interactions, choosing false is strictly better at every locus. -/
def falsePreferred (w : LocalWord 0) : ℚ := if w 0 then 1 / 4 else 3 / 4

/-- A table ignoring its permitted argument gives ties at every state. -/
def tiedTable (_ : LocalWord 0) : ℚ := 1 / 2

/-- All four supplied pair entries satisfy the canonical bounds hypothesis. -/
theorem pairEntries_bounded : ∀ q, pairEntries q ∈ Set.Icc (0 : ℚ) 1 := by
  change ∀ q : Fin 4, pairEntries q ∈ Set.Icc (0 : ℚ) 1
  norm_num [Fin.forall_fin_succ, pairEntries]

/-- The decoded local-word table preserves those entry bounds. -/
theorem pairTable_bounded (w : LocalWord 1) : pairTable w ∈ Set.Icc (0 : ℚ) 1 :=
  pairEntries_bounded (encode w)

/-- The shared cyclic adapter inherits bounds for every state of this fixture. -/
theorem pair_bounded (x : Config 3) :
    sharedCyclic (by decide : 1 < 3) pairTable x ∈ Set.Icc (0 : ℚ) 1 :=
  sharedCyclic_fitness_mem_Icc (by decide) pairTable pairTable_bounded x

/-- Apply rotation invariance at nonzero interaction arity. -/
theorem pair_rotated (x : Config 3) (r : Fin 3) :
    sharedCyclic (by decide : 1 < 3) pairTable (rotate r x) =
      sharedCyclic (by decide) pairTable x :=
  sharedCyclic_fitness_rotate (by decide) pairTable x r

/-- Rotation invariance also applies at maximal permitted arity. -/
theorem full_rotated (x : Config 3) (r : Fin 3) :
    sharedCyclic (by decide : 2 < 3) fullTable (rotate r x) =
      sharedCyclic (by decide) fullTable x :=
  sharedCyclic_fitness_rotate (by decide) fullTable x r

/-- A direct exact value for the forward-window two-slot fixture. -/
theorem pair_value : sharedCyclic (by decide : 1 < 3) pairTable singleLastBit = 5 / 27 := by
  norm_num [sharedCyclic_fitness_eq, pairTable, pairEntries, encode_val,
    Fin.sum_univ_succ, singleLastBit, Fin.ext_iff]

/-- The same state at maximal arity has a distinct exact shared-table quality. -/
theorem full_value : sharedCyclic (by decide : 2 < 3) fullTable singleLastBit = 1 / 7 := by
  norm_num [sharedCyclic_fitness_eq, fullTable, fullEntries, encode_val,
    Fin.sum_univ_succ, singleLastBit, Fin.ext_iff]

/-- The vector adapter and direct shared-table interpretation are the same function. -/
theorem pair_array_interpretation :
    sharedCyclicFromEntries (by decide : 1 < 3) pairEntries = sharedCyclic (by decide) pairTable :=
  rfl

/-- The Hamming formula identifies the two single-true-bit states as equal-quality states. -/
theorem same_hamming_quality (x y : Config 3) (h : hammingWeight x = hammingWeight y) :
    sharedCyclic (by decide : 0 < 3) truePreferred x =
      sharedCyclic (by decide) truePreferred y := by
  simp only [sharedCyclic_K_zero_hamming, h]

/-- The single-last-bit fixture has exactly one true coordinate. -/
theorem singleLast_hamming : hammingWeight singleLastBit = 1 := by
  decide

/-- Instantiate the Hamming-count theorem with rational shared values. -/
theorem k_zero_value : sharedCyclic (by decide : 0 < 3) truePreferred singleLastBit = 5 / 12 := by
  norm_num [sharedCyclic_K_zero_hamming, singleLast_hamming, truePreferred]

/-- Strictly preferring true selects the all-true global maximum through the maximum theorem. -/
theorem truePreferred_maximum :
    IsMaxOn (sharedCyclic (by decide : 0 < 3) truePreferred) Set.univ (fun _ ↦ true) :=
  (sharedCyclic_isMaxOn_iff_all_true (by decide) truePreferred (fun _ ↦ true)
    (by norm_num [truePreferred])).mpr (fun _ ↦ rfl)

/-- The opposite strict preference selects the all-false maximum through the maximum theorem. -/
theorem falsePreferred_maximum :
    IsMaxOn (sharedCyclic (by decide : 0 < 3) falsePreferred) Set.univ (fun _ ↦ false) :=
  (sharedCyclic_isMaxOn_iff_all_false (by decide) falsePreferred (fun _ ↦ false)
    (by norm_num [falsePreferred])).mpr (fun _ ↦ rfl)

/-- The N=1,K=0 boundary includes both tied states as global maxima. -/
theorem singleton_tied (x : Config 1) :
    IsMaxOn (sharedCyclic (by decide : 0 < 1) tiedTable) Set.univ x :=
  sharedCyclic_isMaxOn_of_eq (by decide) tiedTable x rfl

/-- Ignoring the input makes the singleton quality exactly one half at every state. -/
theorem singleton_value (x : Config 1) :
    sharedCyclic (by decide : 0 < 1) tiedTable x = 1 / 2 := by
  simp [sharedCyclic, fitness, contribution, sharedTables, tiedTable]

/-- The locus-specific alternative retains the canonical bound for the separating family. -/
theorem witness_bounded (x : Config 2) :
    locusSpecificCyclic (by decide : 0 < 2) witnessTables x ∈ Set.Icc (0 : ℚ) 1 :=
  locusSpecificCyclic_fitness_mem_Icc (by decide) witnessTables witnessTables_bounded x

/-- The exact witness breaks the equality that every shared table must preserve. -/
theorem witness_labeled_values_differ :
    locusSpecificCyclic (by decide : 0 < 2) witnessTables state01 ≠
      locusSpecificCyclic (by decide : 0 < 2) witnessTables state10 := by
  simp [witness_fitness_state01, witness_fitness_state10]

/--
info: [1 / 2, 1 / 2]
-/
#guard_msgs in
#eval [sharedCyclic (by decide : 0 < 1) tiedTable (fun _ ↦ false),
  sharedCyclic (by decide : 0 < 1) tiedTable (fun _ ↦ true)]

/--
info: [1, 0, 1 / 2, 1 / 2]
-/
#guard_msgs in
#eval [locusSpecificCyclic (by decide : 0 < 2) witnessTables state01,
  locusSpecificCyclic (by decide : 0 < 2) witnessTables state10,
  sharedCyclic (by decide : 0 < 2) truePreferred state01,
  sharedCyclic (by decide : 0 < 2) truePreferred state10]

/--
info: [1, 1]
-/
#guard_msgs in
#eval [hammingWeight singleLastBit, hammingWeight singleMiddleBit]

/--
info: [5 / 12, 5 / 12]
-/
#guard_msgs in
#eval [sharedCyclic (by decide : 0 < 3) truePreferred singleLastBit,
  sharedCyclic (by decide : 0 < 3) truePreferred singleMiddleBit]

/--
info: [0, 1, 2]
-/
#guard_msgs in
#eval List.ofFn (fun i : Fin 3 ↦
  (encode (extract (cyclicTopology (by decide : 1 < 3)) singleLastBit i)).val)

/--
info: [1, 2, 0]
-/
#guard_msgs in
#eval List.ofFn (fun i : Fin 3 ↦
  (encode (extract (cyclicTopology (by decide : 1 < 3)) (rotate 1 singleLastBit) i)).val)

/--
info: [5 / 27, 5 / 27]
-/
#guard_msgs in
#eval [sharedCyclicFromEntries (by decide : 1 < 3) pairEntries singleLastBit,
  sharedCyclic (by decide : 1 < 3) pairTable (rotate 1 singleLastBit)]

/--
info: [1, 2, 4]
-/
#guard_msgs in
#eval List.ofFn (fun i : Fin 3 ↦
  (encode (extract (cyclicTopology (by decide : 2 < 3)) singleLastBit i)).val)

/--
info: [1 / 7, 1 / 7]
-/
#guard_msgs in
#eval [sharedCyclic (by decide : 2 < 3) fullTable singleLastBit,
  sharedCyclic (by decide : 2 < 3) fullTable (rotate 1 singleLastBit)]

end OrgLibExamples.SharedCyclic
