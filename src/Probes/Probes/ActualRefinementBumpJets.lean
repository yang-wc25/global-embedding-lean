import Probes.ActualBoundedRefinementCover
import Smoothing.WeightedActualInverse
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Actual localized refinement cutoffs and uniform full joint derivative bounds

One fixed compactly supported bump is translated and rescaled. Its all-order
constants are chosen before every center, scale and finite cover. In the sum,
inactive derivatives vanish on the real closed supports before the local
5^dim packing count is applied.
-/

noncomputable section
open Set Function Filter Metric
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def actualRefinementUnitBump : ContDiffBump (0 : E) := ⟨1,2,by norm_num,by norm_num⟩

theorem actual_refinement_unit_bump_bounded (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, ‖iteratedFDeriv ℝ j (actualRefinementUnitBump E : E → ℝ) x‖ ≤ C := by
  have hsm : ContDiff ℝ ∞ (actualRefinementUnitBump E : E → ℝ) := (actualRefinementUnitBump E).contDiff
  have hB : BddAbove (range (fun x : E => ‖iteratedFDeriv ℝ j (actualRefinementUnitBump E : E → ℝ) x‖)) := by
    apply (hsm.continuous_iteratedFDeriv
      (by simp)).norm.bddAbove_range_of_hasCompactSupport
    apply HasCompactSupport.comp_left _ norm_zero
    exact (actualRefinementUnitBump E).hasCompactSupport.iteratedFDeriv j
  obtain ⟨C,hC⟩ := hB
  exact ⟨max C 0,le_max_right _ _,fun x => (hC (mem_range_self x)).trans (le_max_left _ _)⟩

def actualRefinementBumpJetCost (j : ℕ) : ℝ :=
  Classical.choose (actual_refinement_unit_bump_bounded E j)

theorem actualRefinementBumpJetCost_nonneg (j : ℕ) : 0 ≤ actualRefinementBumpJetCost E j :=
  (Classical.choose_spec (actual_refinement_unit_bump_bounded E j)).1

theorem actualRefinementBumpJetCost_bound (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (actualRefinementUnitBump E : E → ℝ) x‖ ≤ actualRefinementBumpJetCost E j :=
  (Classical.choose_spec (actual_refinement_unit_bump_bounded E j)).2 x

def actualRefinementBump (r : ℝ) (c : E) : E → ℝ :=
  fun x => actualRefinementUnitBump E (r⁻¹ • (x-c))

theorem actualRefinementBump_eq_native (r : ℝ) (hr : 0 < r) (c : E) :
    actualRefinementBump E r c = (⟨r,2*r,hr,by linarith⟩ : ContDiffBump c) := by
  funext x
  have he : 2*r/r = 2 := by field_simp
  simp only [actualRefinementBump,ContDiffBump.apply,actualRefinementUnitBump,div_one,
    inv_one,one_smul,sub_zero,he]

theorem actualRefinementBump_contDiff (r : ℝ) (c : E) : ContDiff ℝ ∞ (actualRefinementBump E r c) :=
  (actualRefinementUnitBump E).contDiff.comp ((contDiff_id.sub contDiff_const).const_smul r⁻¹)

theorem actualRefinementBump_nonneg (r : ℝ) (c x : E) : 0 ≤ actualRefinementBump E r c x :=
  (actualRefinementUnitBump E).nonneg

theorem actualRefinementBump_le_one (r : ℝ) (c x : E) : actualRefinementBump E r c x ≤ 1 :=
  (actualRefinementUnitBump E).le_one

theorem actualRefinementBump_one (r : ℝ) (hr : 0 < r) (c x : E) (hx : dist x c ≤ r) :
    actualRefinementBump E r c x = 1 := by
  rw [actualRefinementBump_eq_native E r hr c]
  exact ContDiffBump.one_of_mem_closedBall _ hx

theorem actualRefinementBump_tsupport (r : ℝ) (hr : 0 < r) (c : E) :
    tsupport (actualRefinementBump E r c) = closedBall c (2*r) := by
  rw [actualRefinementBump_eq_native E r hr c]
  exact ContDiffBump.tsupport_eq _

/-- Exact dilation preserves the positive slow weight, with every derivative
taken in the full native model, hence in all parameter and spatial directions. -/
theorem actualRefinementBump_weighted_jet (r : ℝ) (hr : 0 < r) (c x : E) (j : ℕ) :
    r^j*‖iteratedFDeriv ℝ j (actualRefinementBump E r c) x‖ ≤ actualRefinementBumpJetCost E j := by
  let u : E → ℝ := actualRefinementUnitBump E
  have he : actualRefinementBump E r c =
      fun y => (u ∘ slowDilation r⁻¹ (inv_ne_zero hr.ne')) (y-c) := rfl
  rw [he,iteratedFDeriv_comp_sub,norm_iteratedFDeriv_slowDilation u r⁻¹ (inv_pos.mpr hr)]
  have hp : r^j*(r⁻¹)^j = 1 := by rw [← mul_pow,mul_inv_cancel₀ hr.ne',one_pow]
  rw [← mul_assoc,hp,one_mul]
  exact actualRefinementBumpJetCost_bound E j _

def actualRefinementRawSum (s : Finset E) (r : ℝ) : E → ℝ :=
  fun x => ∑ c ∈ s, actualRefinementBump E r c x

theorem actualRefinementRawSum_contDiff (s : Finset E) (r : ℝ) :
    ContDiff ℝ ∞ (actualRefinementRawSum E s r) :=
  ContDiff.sum fun c _ => actualRefinementBump_contDiff E r c

theorem actualRefinementRawSum_nonneg (s : Finset E) (r : ℝ) (x : E) :
    0 ≤ actualRefinementRawSum E s r x :=
  Finset.sum_nonneg fun c _ => actualRefinementBump_nonneg E r c x

theorem actualRefinementRawSum_lower_on_cover
    (s : Finset E) (r : ℝ) (hr : 0 < r) (K : Set E)
    (hcover : ∀ x ∈ K, ∃ c ∈ s, dist x c ≤ r) (x : E) (hx : x ∈ K) :
    1 ≤ actualRefinementRawSum E s r x := by
  obtain ⟨c,hcs,hxc⟩ := hcover x hx
  rw [← actualRefinementBump_one E r hr c x hxc]
  exact Finset.single_le_sum (fun a _ => actualRefinementBump_nonneg E r a x) hcs

theorem actualRefinementRawSum_weighted_jet
    (s : Finset E) (r : ℝ) (hr : 0 < r)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → r ≤ dist a b) (j : ℕ) (x : E) :
    r^j*‖iteratedFDeriv ℝ j (actualRefinementRawSum E s r) x‖ ≤
      (5^Module.finrank ℝ E : ℕ)*actualRefinementBumpJetCost E j := by
  classical
  let active := s.filter (fun a => dist a x ≤ 2*r)
  have hzero (a : E) (ha : a ∈ s) (hn : a ∉ active) :
      iteratedFDeriv ℝ j (actualRefinementBump E r a) x = 0 := by
    have hnot : x ∉ tsupport (actualRefinementBump E r a) := by
      rw [actualRefinementBump_tsupport E r hr a]
      intro hx
      exact hn (Finset.mem_filter.mpr ⟨ha,by simpa only [mem_closedBall,dist_comm] using hx⟩)
    by_contra hh
    exact hnot (support_iteratedFDeriv_subset j hh)
  have hsum : (∑ a ∈ s, iteratedFDeriv ℝ j (actualRefinementBump E r a) x) =
      ∑ a ∈ active, iteratedFDeriv ℝ j (actualRefinementBump E r a) x :=
    (Finset.sum_subset (Finset.filter_subset _ _) (fun a ha hn => hzero a ha hn)).symm
  change r^j*‖iteratedFDeriv ℝ j (fun y => ∑ a ∈ s, actualRefinementBump E r a y) x‖ ≤ _
  rw [iteratedFDeriv_fun_sum_apply (fun a _ =>
    ((actualRefinementBump_contDiff E r a).contDiffAt.of_le (by simp))),hsum]
  calc
    _ ≤ r^j*(∑ a ∈ active, ‖iteratedFDeriv ℝ j (actualRefinementBump E r a) x‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg hr.le j)
    _ = ∑ a ∈ active, r^j*‖iteratedFDeriv ℝ j (actualRefinementBump E r a) x‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ _a ∈ active, actualRefinementBumpJetCost E j :=
      Finset.sum_le_sum (fun a _ => actualRefinementBump_weighted_jet E r hr a x j)
    _ = (active.card : ℝ)*actualRefinementBumpJetCost E j := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast actual_separated_local_refinement_count s r hr hsep x)
      (actualRefinementBumpJetCost_nonneg E j)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualRefinementBump_weighted_jet
#print axioms GlobalEmbedding.Continuation.actualRefinementRawSum_weighted_jet
