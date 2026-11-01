import OrgLib
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Kernel axiom audit

Check the codec, table interpretations, topology constructor, exact source-shaped
fitness theorem, and inherited bounds/maximality against standard Lean axioms.
-/

open OrgLib.NK

run_cmd do
  for name in [``OrgLib.NK.wordEquiv, ``OrgLib.NK.encode, ``OrgLib.NK.decode,
      ``OrgLib.NK.encode_decode, ``OrgLib.NK.decode_encode, ``OrgLib.NK.encode_val,
      ``OrgLib.NK.tablesFromEntries, ``OrgLib.NK.lookup_eq, ``OrgLib.NK.rIndex,
      ``OrgLib.NK.rIndex_pos, ``OrgLib.NK.rIndex_le, ``OrgLib.NK.rIndex_sub_one,
      ``OrgLib.NK.lookup_rIndex, ``OrgLib.NK.entriesFromTables,
      ``OrgLib.NK.tablesFromEntries_entriesFromTables,
      ``OrgLib.NK.entriesFromTables_tablesFromEntries,
      ``OrgLib.NK.Topology.ofNeighbors,
      ``OrgLib.NK.Topology.ofNeighbors_scope_zero,
      ``OrgLib.NK.Topology.ofNeighbors_scope_succ,
      ``OrgLib.NK.extract_ofNeighbors,
      ``OrgLib.NK.fitness_eq_indexedAverage,
      ``OrgLib.NK.indexed_fitness_mem_Icc,
      ``indexed_isOneBitLocalMax_iff_isMaxOn_K_zero] do
    let unexpected := (← Lean.collectAxioms name).filter fun ax ↦
      !(([``propext, ``Classical.choice, ``Quot.sound] : List Lean.Name).contains ax)
    unless unexpected.isEmpty do
      throwError "Unexpected axioms in {name}: {unexpected}"

#print axioms OrgLib.NK.encode_decode
#print axioms OrgLib.NK.decode_encode
#print axioms OrgLib.NK.encode_val
#print axioms OrgLib.NK.fitness_eq_indexedAverage
