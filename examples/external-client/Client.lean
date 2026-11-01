import OrgLib

/-!
# A separate researcher's canonical NK client

This client defines its own data and imports only the public library. It does not
reuse the paper fixtures or edit either paper development.
-/

namespace OrgLibClient

open OrgLib.NK

/-- Two uncoupled loci, each reading only its own bit. -/
def topology : Topology 2 0 where
  k_lt_n := by decide
  scope i := ⟨fun _ ↦ i, fun a b _ ↦ (Fin.eq_zero a).trans (Fin.eq_zero b).symm⟩
  self := fun _ ↦ rfl

/-- The loci gain one and one half, respectively, when their bit is true. -/
def tables : Tables 2 0 ℚ :=
  fun i w ↦ if w 0 then (if i = 0 then 1 else 1 / 2) else 0

/-- Both loci choose their preferred bit. -/
def best : Config 2 := fun _ ↦ true

/-- The explicit data satisfy the bound hypothesis of the reusable theorem. -/
theorem tables_bounded (i : Fin 2) (w : LocalWord 0) :
    tables i w ∈ Set.Icc (0 : ℚ) 1 := by
  unfold tables
  split_ifs <;> norm_num

/-- The generic bound applies to every state of this new instance. -/
theorem bounded (x : Config 2) : fitness topology tables x ∈ Set.Icc (0 : ℚ) 1 :=
  fitness_mem_Icc topology tables tables_bounded x

/-- Exact computation is a kernel-checked equality on this finite instance. -/
theorem best_value : fitness topology tables best = 3 / 4 := by
  norm_num [fitness, contribution, extract, topology, tables, best, Fin.sum_univ_succ]

/-- Check the two one-bit comparisons. -/
theorem best_local : IsOneBitLocalMax (fitness topology tables) best := by
  norm_num [IsOneBitLocalMax, fitness, contribution, extract, topology, tables, best,
    OrgLib.NK.flip, Function.update, Fin.forall_fin_succ, Fin.sum_univ_succ]

/-- Obtain global maximality from the generic K=0 result. -/
theorem best_global : IsMaxOn (fitness topology tables) Set.univ best :=
  (isOneBitLocalMax_iff_isMaxOn_K_zero topology tables best).mp best_local

/-- The rational computation has the same real interpretation. -/
theorem exact_real_interpretation (x : Config 2) :
    ((fitness topology tables x : ℚ) : ℝ) =
      fitness topology (fun i w ↦ (tables i w : ℝ)) x :=
  fitness_ratCast topology tables x

/--
info: 3 / 4
-/
#guard_msgs in
#eval fitness topology tables best

end OrgLibClient
