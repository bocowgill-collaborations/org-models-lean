import OrgLib.NK.Ensembles
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.NormNum

/-!
# Two-entry rectangles in the continuous NK table law

At each locus, require one selected entry to exceed one half and a distinct entry
to be at most one half. The nested finite product law assigns this rectangle mass
`(1 / 4)^N`. Unselected entries remain unrestricted; no discrete approximation is used.
-/

noncomputable section

namespace OrgLib.NK

open MeasureTheory Set
open scoped BigOperators

variable {N K : ℕ}

/-- The upper half-line has mass one half under uniform measure on the unit interval. -/
theorem unitUniform_Ioi_half : unitUniform (Ioi (1 / 2 : ℝ)) = (1 / 2 : ENNReal) := by
  rw [unitUniform, Measure.restrict_apply measurableSet_Ioi]
  have he : Ioi (1 / 2 : ℝ) ∩ Icc 0 1 = Ioc (1 / 2 : ℝ) 1 := by
    ext x
    simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]
    exact ⟨fun h ↦ ⟨h.1, h.2.2⟩,
      fun h ↦ ⟨h.1, le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) (le_of_lt h.1), h.2⟩⟩
  rw [he, Real.volume_Ioc]
  norm_num [ENNReal.ofReal_div_of_pos]

/-- The lower closed half-line also has mass one half under the continuous uniform law. -/
theorem unitUniform_Iic_half : unitUniform (Iic (1 / 2 : ℝ)) = (1 / 2 : ENNReal) := by
  rw [unitUniform, Measure.restrict_apply measurableSet_Iic]
  have he : Iic (1 / 2 : ℝ) ∩ Icc 0 1 = Icc (0 : ℝ) (1 / 2) := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    exact ⟨fun h ↦ ⟨h.2.1, h.1⟩,
      fun h ↦ ⟨h.2, h.1, le_trans h.2 (by norm_num : (1 / 2 : ℝ) ≤ 1)⟩⟩
  rw [he, Real.volume_Icc]
  norm_num [ENNReal.ofReal_div_of_pos]

/-- Require an upper and lower selected entry at every locus, leaving all others free. -/
def entryRectangle (wx wy : Fin N → LocalWord K) : Set (Tables N K ℝ) :=
  {c | ∀ i, (1 / 2 : ℝ) < c i (wx i) ∧ c i (wy i) ≤ 1 / 2}

/-- Entry constraints form a measurable event in the finite product table space. -/
theorem measurableSet_entryRectangle (wx wy : Fin N → LocalWord K) :
    MeasurableSet (entryRectangle wx wy) := by
  have hm (i : Fin N) (w : LocalWord K) : Measurable (fun c : Tables N K ℝ ↦ c i w) :=
    (measurable_pi_apply w).comp (measurable_pi_apply i)
  have hc : Measurable (fun _ : Tables N K ℝ ↦ (1 / 2 : ℝ)) := measurable_const
  simpa only [entryRectangle, setOf_forall, setOf_and] using
    (MeasurableSet.iInter fun i ↦
      (measurableSet_lt hc (hm i (wx i))).inter (measurableSet_le (hm i (wy i)) hc))

private theorem prod_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w v : ι) (h : w ≠ v) (a b : ENNReal) :
    (∏ q : ι, if q = w then a else if q = v then b else 1) = a * b := by
  have he (q : ι) : (if q = w then a else if q = v then b else 1) =
      (if q = w then a else 1) * (if q = v then b else 1) := by
    split_ifs <;> simp_all
  simp_rw [he]
  rw [Finset.prod_mul_distrib]
  simp

private def entryWindow (high low : LocalWord K) (w : LocalWord K) : Set ℝ :=
  if w = high then Ioi (1 / 2) else if w = low then Iic (1 / 2) else univ

private theorem tableUniform_two_entries (high low : LocalWord K) (hne : high ≠ low) :
    tableUniform K {φ | (1 / 2 : ℝ) < φ high ∧ φ low ≤ 1 / 2} = (1 / 4 : ENNReal) := by
  have he : {φ | (1 / 2 : ℝ) < φ high ∧ φ low ≤ 1 / 2} =
      Set.univ.pi (entryWindow high low) := by
    ext φ
    simp only [mem_setOf_eq, mem_pi, mem_univ, true_implies]
    constructor
    · intro h w
      by_cases hw : w = high
      · simpa [entryWindow, hw] using h.1
      · by_cases hv : w = low
        · simpa [entryWindow, hw, hv, hne.symm] using h.2
        · simp [entryWindow, hw, hv]
    · intro h
      exact ⟨by simpa [entryWindow] using h high,
        by simpa [entryWindow, hne.symm] using h low⟩
  rw [he, tableUniform, Measure.pi_pi]
  have hm (w : LocalWord K) : unitUniform (entryWindow high low w) =
      if w = high then (1 / 2 : ENNReal) else if w = low then 1 / 2 else 1 := by
    unfold entryWindow
    split_ifs
    · exact unitUniform_Ioi_half
    · exact unitUniform_Iic_half
    · exact measure_univ
  simp_rw [hm]
  rw [prod_two high low hne]
  simp only [one_div]
  rw [← ENNReal.mul_inv (by simp) (by simp)]
  norm_num

/-- Distinct upper/lower entries at each locus give mass one quarter per locus. -/
theorem independentTablesUniform_entryRectangle
    (wx wy : Fin N → LocalWord K) (hne : ∀ i, wx i ≠ wy i) :
    independentTablesUniform N K (entryRectangle wx wy) = (1 / 4 : ENNReal) ^ N := by
  have he : entryRectangle wx wy =
      Set.univ.pi (fun i ↦ {φ | (1 / 2 : ℝ) < φ (wx i) ∧ φ (wy i) ≤ 1 / 2}) := by
    ext c
    simp [entryRectangle]
  rw [he, independentTablesUniform, Measure.pi_pi]
  calc
    _ = ∏ _i : Fin N, (1 / 4 : ENNReal) :=
      Finset.prod_congr rfl (fun i _ ↦ tableUniform_two_entries (wx i) (wy i) (hne i))
    _ = (1 / 4 : ENNReal) ^ N := by simp

end OrgLib.NK

end
