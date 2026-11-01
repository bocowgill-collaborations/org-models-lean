import OrgLib
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Release headline axiom reports

The release repeats the rejection guard for nine headline results and prints their
dependencies together in the build log. These overlap with the core audits;
repeating a rejection guard does not add a distinct mathematical result.
-/

run_cmd do
  for name in [``OrgLib.NK.fitness_mem_Icc,
      ``OrgLib.NK.isOneBitLocalMax_iff_isMaxOn_K_zero,
      ``OrgLib.NK.fitness_reindex_slots,
      ``OrgLib.NK.fitness_eq_indexedAverage,
      ``OrgLib.NK.SharedCyclic.sharedCyclic_fitness_rotate,
      ``OrgLib.NK.SharedCyclic.witness_no_shared_representation,
      ``OrgLib.NK.fitness_ratCast,
      ``OrgLib.NK.SharedCyclic.shared_independent_laws_ne,
      ``OrgLib.NK.SharedCyclic.landscape_laws_ne_N12] do
    let unexpected := (← Lean.collectAxioms name).filter fun ax ↦
      !(([``propext, ``Classical.choice, ``Quot.sound] : List Lean.Name).contains ax)
    unless unexpected.isEmpty do
      throwError "Unexpected axioms in {name}: {unexpected}"

#print axioms OrgLib.NK.fitness_mem_Icc
#print axioms OrgLib.NK.isOneBitLocalMax_iff_isMaxOn_K_zero
#print axioms OrgLib.NK.fitness_reindex_slots
#print axioms OrgLib.NK.fitness_eq_indexedAverage
#print axioms OrgLib.NK.SharedCyclic.sharedCyclic_fitness_rotate
#print axioms OrgLib.NK.SharedCyclic.witness_no_shared_representation
#print axioms OrgLib.NK.fitness_ratCast
#print axioms OrgLib.NK.SharedCyclic.shared_independent_laws_ne
#print axioms OrgLib.NK.SharedCyclic.landscape_laws_ne_N12
