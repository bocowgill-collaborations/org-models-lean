import OrgLib.NK.Ensembles
import OrgLib.NK.EnsembleRectangles
import OrgLib.NK.SharedCyclic.Separation

/-!
# Separation of continuous evaluated-landscape laws

The observable event compares quality at two fixed labeled configurations. Shared
cyclic tables exclude it when the configurations are rotations. Independent
continuous entries give it positive mass through a measurable finite rectangle.
These statements concern idealized continuous laws at fixed topology, not R's RNG.
-/

noncomputable section

namespace OrgLib.NK.SharedCyclic

open OrgLib.NK MeasureTheory
open scoped BigOperators ENNReal

variable {N K : ℕ}

/-- A measurable quality event on two fixed labeled configurations. -/
def landscapeEvent (x y : Config N) : Set (Config N → ℝ) :=
  {F | (1 / 2 : ℝ) < F x ∧ F y ≤ 1 / 2}

/-- Both quality comparisons are measurable coordinate events. -/
theorem measurableSet_landscapeEvent (x y : Config N) :
    MeasurableSet (landscapeEvent x y) :=
  (measurableSet_lt measurable_const (measurable_pi_apply x)).inter
    (measurableSet_le (measurable_pi_apply y) measurable_const)

/-- If every selected entry exceeds one half, its nonempty average does too. -/
theorem fitness_gt_half_of_entries_gt (T : Topology N K) (c : Tables N K ℝ)
    (x : Config N) (hc : ∀ i, (1 / 2 : ℝ) < c i (extract T x i)) :
    (1 / 2 : ℝ) < fitness T c x := by
  rw [fitness, lt_div_iff₀ (Nat.cast_pos.mpr T.n_pos)]
  simpa [contribution, mul_comm] using Finset.sum_lt_sum_of_nonempty
    (show (Finset.univ : Finset (Fin N)).Nonempty from
      ⟨⟨0, T.n_pos⟩, Finset.mem_univ _⟩) (fun i _ ↦ hc i)

/-- If every selected entry is at most one half, its average is at most one half. -/
theorem fitness_le_half_of_entries_le (T : Topology N K) (c : Tables N K ℝ)
    (x : Config N) (hc : ∀ i, c i (extract T x i) ≤ (1 / 2 : ℝ)) :
    fitness T c x ≤ (1 / 2 : ℝ) := by
  rw [fitness, div_le_iff₀ (Nat.cast_pos.mpr T.n_pos)]
  simpa [contribution, mul_comm] using Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hc i)

/-- Shared cyclic symmetry makes the rotated-state event's preimage empty. -/
theorem shared_event_preimage_empty (hKN : K < N) (x : Config N) (r : Fin N) :
    sharedRealization hKN ⁻¹' landscapeEvent x (rotate r x) = ∅ := by
  ext φ
  simp [sharedRealization, landscapeEvent, fitness_shared_rotate]

/-- A rotated-state event has zero mass under every shared cyclic law. -/
theorem shared_event_zero_of_rotate (hKN : K < N) (x : Config N) (r : Fin N) :
    sharedUniformCyclic hKN (landscapeEvent x (rotate r x)) = 0 := by
  rw [sharedUniformCyclic,
    Measure.map_apply (measurable_sharedRealization hKN) (measurableSet_landscapeEvent _ _),
    shared_event_preimage_empty]
  exact measure_empty

/-- The selected-entry rectangle implies the observable quality event. -/
theorem entryRectangle_subset_event_preimage (T : Topology N K) (x y : Config N) :
    entryRectangle (fun i ↦ extract T x i) (fun i ↦ extract T y i) ⊆
      independentRealization T ⁻¹' landscapeEvent x y := by
  intro c hc
  exact ⟨fitness_gt_half_of_entries_gt T c x (fun i ↦ (hc i).1),
    fitness_le_half_of_entries_le T c y (fun i ↦ (hc i).2)⟩

/-- Distinct selected words give a positive lower bound on the independent event mass. -/
theorem independent_event_lower_bound (T : Topology N K) (x y : Config N)
    (hd : ∀ i, extract T x i ≠ extract T y i) :
    (1 / 4 : ENNReal) ^ N ≤ independentUniform T (landscapeEvent x y) := by
  rw [independentUniform,
    Measure.map_apply (measurable_independentRealization T) (measurableSet_landscapeEvent x y)]
  calc
    _ = independentTablesUniform N K
        (entryRectangle (fun i ↦ extract T x i) (fun i ↦ extract T y i)) :=
      (independentTablesUniform_entryRectangle _ _ hd).symm
    _ ≤ _ := measure_mono (entryRectangle_subset_event_preimage T x y)

/-- Rotation-related configurations with distinct local words distinguish the cyclic laws. -/
theorem cyclic_landscape_laws_ne (hKN : K < N) (x : Config N) (r : Fin N)
    (hd : ∀ i, extract (cyclicTopology hKN) x i ≠
      extract (cyclicTopology hKN) (rotate r x) i) :
    sharedUniformCyclic hKN ≠ independentUniformCyclic hKN := by
  intro he
  have hb := independent_event_lower_bound (cyclicTopology hKN) x (rotate r x) hd
  change (1 / 4 : ENNReal) ^ N ≤
    independentUniformCyclic hKN (landscapeEvent x (rotate r x)) at hb
  rw [← he, shared_event_zero_of_rotate] at hb
  exact (not_le_of_gt (ENNReal.pow_pos (by norm_num : (0 : ENNReal) < 1 / 4) N)) hb

/-- The two labeled states select different local words at each locus. -/
theorem extract_state01_ne_state10 : ∀ i,
    extract (cyclicTopology (by decide : 0 < 2)) state01 i ≠
      extract (cyclicTopology (by decide : 0 < 2)) state10 i := by
  decide

/-- T14: the shared continuous law assigns the observable event zero mass. -/
theorem shared_event_state01_state10 :
    sharedUniformCyclic (by decide : 0 < 2) (landscapeEvent state01 state10) = 0 := by
  simpa only [rotate_state01] using
    shared_event_zero_of_rotate (by decide : 0 < 2) state01 (1 : Fin 2)

/-- T14: independent continuous entries give the observable event mass at least 1/16. -/
theorem independent_event_state01_state10 :
    (1 / 16 : ENNReal) ≤
      independentUniformCyclic (by decide : 0 < 2) (landscapeEvent state01 state10) := by
  have h := independent_event_lower_bound (cyclicTopology (by decide : 0 < 2))
    state01 state10 extract_state01_ne_state10
  norm_num [← ENNReal.inv_pow, independentUniformCyclic] at h ⊢
  exact h

/-- T14: the shared and independent evaluated-landscape laws are different. -/
theorem shared_independent_laws_ne :
    sharedUniformCyclic (by decide : 0 < 2) ≠ independentUniformCyclic (by decide : 0 < 2) := by
  apply cyclic_landscape_laws_ne (by decide : 0 < 2) state01 (1 : Fin 2)
  simpa only [rotate_state01] using extract_state01_ne_state10

end OrgLib.NK.SharedCyclic

end
