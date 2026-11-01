import OrgLib
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Kernel axiom audit

This build-time check rejects unproved placeholders and any nonstandard axiom in
the transitive dependencies of the public core definitions, proofs, and action laws.
It does not certify that the mathematical specification matches an external R program.
-/

run_cmd do
  for name in [``OrgLib.NK.Topology.n_pos, ``OrgLib.NK.extract, ``OrgLib.NK.contribution,
      ``OrgLib.NK.fitness, ``OrgLib.NK.flip, ``OrgLib.NK.IsOneBitLocalMax,
      ``OrgLib.NK.contribution_eq_of_agree_on_scope, ``OrgLib.NK.extract_K_zero,
      ``OrgLib.NK.fitness_K_zero, ``OrgLib.NK.fitness_mem_Icc,
      ``OrgLib.NK.fitness_flip_le_iff_K_zero, ``OrgLib.NK.isOneBitLocalMax_iff_isMaxOn_K_zero,
      ``OrgLib.NK.Topology.reindex, ``OrgLib.NK.reindexTables,
      ``OrgLib.NK.extract_reindex, ``OrgLib.NK.contribution_reindex_slots,
      ``OrgLib.NK.fitness_reindex_slots, ``OrgLib.NK.Topology.reindex_refl,
      ``OrgLib.NK.reindexTables_refl, ``OrgLib.NK.Topology.reindex_reindex,
      ``OrgLib.NK.reindexTables_reindex] do
    let unexpected := (← Lean.collectAxioms name).filter fun ax ↦
      !(([``propext, ``Classical.choice, ``Quot.sound] : List Lean.Name).contains ax)
    unless unexpected.isEmpty do
      throwError "Unexpected axioms in {name}: {unexpected}"

#print axioms OrgLib.NK.contribution_eq_of_agree_on_scope
#print axioms OrgLib.NK.fitness_mem_Icc
#print axioms OrgLib.NK.fitness_K_zero
#print axioms OrgLib.NK.isOneBitLocalMax_iff_isMaxOn_K_zero
#print axioms OrgLib.NK.fitness_reindex_slots
