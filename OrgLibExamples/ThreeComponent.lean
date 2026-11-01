import OrgLib
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/-!
# A three-component NK landscape

The data reproduce the worked example in Csaszar, *A note on how NK landscapes
work* (2018), p. 3, DOI 10.1186/s41469-018-0039-0. Global coordinates are screen,
battery and CPU; local orders are screen–CPU, battery–screen and CPU–battery.
Rows use addresses `00,01,10,11`. The representation and theorem names are generic.
All eight values below are exact rational theorems about canonical NK fitness.
-/

namespace OrgLibExamples.ThreeComponent

open OrgLib.NK

/-- Contribution values for the three loci, in MSB-first address order. -/
def entryData : Vector (Vector ℚ 4) 3 :=
  ⟨#[⟨#[9 / 10, 1 / 2, 3 / 10, 7 / 10], rfl⟩,
    ⟨#[4 / 5, 0, 0, 3 / 10], rfl⟩, ⟨#[1 / 10, 1 / 2, 1 / 5, 9 / 10], rfl⟩], rfl⟩

def entries : TableEntries 3 1 ℚ := fun i q ↦ (entryData.get i).get q

def neighborData : Vector (Vector (Fin 3) 1) 3 :=
  ⟨#[⟨#[2], rfl⟩, ⟨#[0], rfl⟩, ⟨#[1], rfl⟩], rfl⟩

def neighborAt : Fin 3 → Fin 1 → Fin 3 := fun i j ↦ (neighborData.get i).get j

def neighbors (i : Fin 3) : Fin 1 ↪ Fin 3 where
  toFun := neighborAt i
  inj' := (by decide : ∀ i : Fin 3, Function.Injective (neighborAt i)) i

theorem neighbors_nonfocal : ∀ i j, neighbors i j ≠ i := by decide

def topology : Topology 3 1 := Topology.ofNeighbors (by decide) neighbors neighbors_nonfocal

def evaluate : Config 3 → ℚ := fitness topology (tablesFromEntries entries)

local macro "three_component_value" q:term "," bits:term : tactic =>
  `(tactic| norm_num [evaluate, fitness, contribution, tablesFromEntries, entries,
    entryData, Vector.get, topology, extract_ofNeighbors, encode_val,
    neighbors, neighborAt, neighborData, Fin.sum_univ_succ,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
    show decode ($q : Fin 8) = $bits by decide])

theorem expected_code_0 : evaluate (decode (0 : Fin 8)) = 3 / 5 := by
  three_component_value 0, ![false, false, false]

theorem expected_code_1 : evaluate (decode (1 : Fin 8)) = 1 / 2 := by
  three_component_value 1, ![false, false, true]

theorem expected_code_2 : evaluate (decode (2 : Fin 8)) = 7 / 15 := by
  three_component_value 2, ![false, true, false]

theorem expected_code_3 : evaluate (decode (3 : Fin 8)) = 7 / 15 := by
  three_component_value 3, ![false, true, true]

theorem expected_code_4 : evaluate (decode (4 : Fin 8)) = 2 / 15 := by
  three_component_value 4, ![true, false, false]

theorem expected_code_5 : evaluate (decode (5 : Fin 8)) = 3 / 10 := by
  three_component_value 5, ![true, false, true]

theorem expected_code_6 : evaluate (decode (6 : Fin 8)) = 11 / 30 := by
  three_component_value 6, ![true, true, false]

theorem expected_code_7 : evaluate (decode (7 : Fin 8)) = 19 / 30 := by
  three_component_value 7, ![true, true, true]

end OrgLibExamples.ThreeComponent
