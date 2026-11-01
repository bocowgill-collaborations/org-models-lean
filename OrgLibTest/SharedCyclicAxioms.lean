import OrgLib
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Kernel axiom audit

Check the cyclic core, sharedCyclic constructors, symmetry, count/maximality properties,
and fixed-label rational separation against standard Lean axioms.
-/

open OrgLib.NK.SharedCyclic

run_cmd do
  for name in [``OrgLib.NK.cyclicTopology, ``OrgLib.NK.sharedTables, ``OrgLib.NK.rotate,
      ``OrgLib.NK.cyclicTopology_scope_val, ``OrgLib.NK.extract_cyclic,
      ``OrgLib.NK.rotate_apply, ``OrgLib.NK.rotate_apply_mod,
      ``OrgLib.NK.extract_cyclic_rotate, ``OrgLib.NK.fitness_shared_rotate,
      ``sharedCyclic, ``locusSpecificCyclic, ``locusSpecificCyclic_sharedTables,
      ``sharedCyclicFromEntries, ``sharedCyclic_fitness_eq, ``sharedCyclic_entries_fitness_eq,
      ``sharedCyclic_fitness_rotate, ``sharedCyclic_fitness_mem_Icc,
      ``locusSpecificCyclic_fitness_mem_Icc,
      ``hammingWeight, ``hammingWeight_le, ``card_false_eq_sub_hammingWeight,
      ``sharedCyclic_K_zero_hamming, ``sharedCyclic_isMaxOn_iff_all_true,
      ``sharedCyclic_isMaxOn_iff_all_false, ``sharedCyclic_isMaxOn_of_eq,
      ``state01, ``state10, ``witnessTables, ``witnessTables_bounded,
      ``witness_fitness_state01, ``witness_fitness_state10,
      ``rotate_state01, ``sharedCyclic_state01_eq_state10, ``witness_no_shared_representation] do
    let unexpected := (← Lean.collectAxioms name).filter fun ax ↦
      !(([``propext, ``Classical.choice, ``Quot.sound] : List Lean.Name).contains ax)
    unless unexpected.isEmpty do
      throwError "Unexpected axioms in {name}: {unexpected}"

#print axioms sharedCyclic_fitness_eq
#print axioms sharedCyclic_fitness_rotate
#print axioms sharedCyclic_K_zero_hamming
#print axioms sharedCyclic_isMaxOn_iff_all_true
#print axioms sharedCyclic_isMaxOn_iff_all_false
#print axioms sharedCyclic_isMaxOn_of_eq
#print axioms witness_no_shared_representation
