import OrgLib.NK.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Filter.Extr

/-!
# Ordered properties of canonical NK fitness

Bounded tables produce bounded average fitness. With no interactions (`K = 0`),
the average is separable across loci, so weak one-bit local and global maximality
coincide. The maximality theorem allows ties and arbitrary table values; it requires
neither value bounds nor distributional assumptions.

-/

namespace OrgLib.NK

open scoped BigOperators

variable {N K : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- T02: averaging contribution values in the unit interval stays in the unit interval. -/
theorem fitness_mem_Icc (T : Topology N K) (c : Tables N K R)
    (hc : ∀ i w, c i w ∈ Set.Icc (0 : R) 1) (x : Config N) :
    fitness T c x ∈ Set.Icc (0 : R) 1 := by
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun i _ ↦ (hc i (extract T x i)).1)
      (Nat.cast_nonneg N)
  · apply (div_le_iff₀ (Nat.cast_pos.mpr T.n_pos)).mpr
    simpa using Finset.sum_le_sum (s := Finset.univ)
      (fun i _ ↦ (hc i (extract T x i)).2)

/-- At zero interactions, comparing a flip's fitness reduces to its focal table values. -/
theorem fitness_flip_le_iff_K_zero
    (T : Topology N 0) (c : Tables N 0 R) (x : Config N) (i : Fin N) :
    fitness T c (flip x i) ≤ fitness T c x ↔
      c i (fun _ ↦ !x i) ≤ c i (fun _ ↦ x i) := by
  rw [fitness_K_zero, fitness_K_zero,
    div_le_div_iff_of_pos_right (Nat.cast_pos.mpr T.n_pos)]
  simp_rw [flip, Function.apply_update (fun j b ↦ c j (fun _ ↦ b))]
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_le_add_iff_right]

/-- T04: at zero interactions, weak one-bit local maxima are exactly global maxima. -/
theorem isOneBitLocalMax_iff_isMaxOn_K_zero
    (T : Topology N 0) (c : Tables N 0 R) (x : Config N) :
    IsOneBitLocalMax (fitness T c) x ↔ IsMaxOn (fitness T c) Set.univ x := by
  constructor
  · intro hx
    apply isMaxOn_univ_iff.mpr
    intro y
    rw [fitness_K_zero, fitness_K_zero,
      div_le_div_iff_of_pos_right (Nat.cast_pos.mpr T.n_pos)]
    apply Finset.sum_le_sum
    intro i _
    rcases Bool.eq_or_eq_not (y i) (x i) with h | h
    · simp only [h, le_refl]
    · simpa only [h] using (fitness_flip_le_iff_K_zero T c x i).mp (hx i)
  · exact fun hx i ↦ isMaxOn_univ_iff.mp hx (flip x i)

end OrgLib.NK
