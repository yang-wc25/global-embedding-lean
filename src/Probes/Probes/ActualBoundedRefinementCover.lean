import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

/-!
# Actual finite refinement centers with a dimension-only local count

A maximal separated subset of the original bounded piece supplies the cover.
The number of all centers is not used in the local bound. After translation
and rescaling, the native Besicovitch packing estimate bounds the centers
whose radius-two balls can meet a point by 5^dim.
-/

noncomputable section
open Set Function Metric
open scoped NNReal ENNReal
namespace GlobalEmbedding.Continuation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem actual_separated_local_refinement_count
    (s : Finset E) (r : ℝ) (hr : 0 < r)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → r ≤ dist a b) (x : E) :
    (s.filter (fun a => dist a x ≤ 2*r)).card ≤ 5^Module.finrank ℝ E := by
  classical
  let t := s.filter (fun a => dist a x ≤ 2*r)
  let f : E → E := fun a => r⁻¹ • (a-x)
  have hf : Injective f := by
    intro a b hab
    have hh := congrArg (fun y : E => r • y) hab
    simpa only [f,smul_inv_smul₀ hr.ne',sub_left_inj] using hh
  have hball : ∀ y ∈ t.image f, ‖y‖ ≤ 2 := by
    intro y hy
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hy
    have ha2 := (Finset.mem_filter.mp ha).2
    change ‖r⁻¹ • (a-x)‖ ≤ 2
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le),← div_eq_inv_mul]
    apply (div_le_iff₀ hr).2
    simpa only [dist_eq_norm] using ha2
  have hdist : ∀ y ∈ t.image f, ∀ z ∈ t.image f, y ≠ z → 1 ≤ ‖y-z‖ := by
    intro y hy z hz hyz
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hz
    have hab : a ≠ b := fun hh => hyz (congrArg f hh)
    have hdis := hsep a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab
    change 1 ≤ ‖r⁻¹ • (a-x)-r⁻¹ • (b-x)‖
    rw [← smul_sub,sub_sub_sub_cancel_right,norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hr.le),← div_eq_inv_mul]
    apply (le_div_iff₀ hr).2
    simpa only [one_mul,dist_eq_norm] using hdis
  have hh := Besicovitch.card_le_of_separated (t.image f) hball hdist
  rwa [Finset.card_image_of_injective t hf] at hh

/-- The original set need only be totally bounded in the original model.
No compactness of the whole source manifold is introduced. -/
theorem actual_exists_finite_bounded_refinement
    (K : Set E) (hK : TotallyBounded K) (r : ℝ) (hr : 0 < r) :
    ∃ s : Finset E,
      (↑s : Set E) ⊆ K ∧
      (∀ a ∈ s, ∀ b ∈ s, a ≠ b → r ≤ dist a b) ∧
      (∀ x ∈ K, ∃ a ∈ s, dist x a ≤ r) ∧
      ∀ x : E, (s.filter (fun a => dist a x ≤ 2*r)).card ≤ 5^Module.finrank ℝ E := by
  classical
  let d : ℝ≥0 := ⟨r,hr.le⟩
  have hd : d ≠ 0 := by
    intro hz
    exact hr.ne' (congrArg (fun t : ℝ≥0 => (t : ℝ)) hz)
  have hd2 : d/2 ≠ 0 := div_ne_zero hd (by norm_num)
  obtain ⟨N,hNK,hNfin,hNc⟩ := exists_finite_isCover_of_totallyBounded hd2 hK
  have hE : externalCoveringNumber (d/2) K < ⊤ :=
    hNc.externalCoveringNumber_le_encard.trans_lt hNfin.encard_lt_top
  have hp := packingNumber_two_mul_le_externalCoveringNumber (d/2) K
  have he : 2*(d/2) = d := by ring
  rw [he] at hp
  have hpfin : packingNumber d K ≠ ⊤ := (hp.trans_lt hE).ne
  let S := maximalSeparatedSet d K
  have hSfin : S.Finite := Set.encard_ne_top_iff.mp (by
    rw [show S.encard = packingNumber d K from encard_maximalSeparatedSet hpfin]
    exact hpfin)
  let s := hSfin.toFinset
  have hsK : (↑s : Set E) ⊆ K := by
    simpa only [s,Set.Finite.coe_toFinset] using (maximalSeparatedSet_subset (ε := d) (A := K))
  have hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → r ≤ dist a b := by
    intro a ha b hb hab
    have haS : a ∈ S := hSfin.mem_toFinset.mp ha
    have hbS : b ∈ S := hSfin.mem_toFinset.mp hb
    have hs := (isSeparated_maximalSeparatedSet (ε := d) (A := K)) haS hbS hab
    have hn : d < nndist a b := by
      change (d : ℝ≥0∞) < edist a b at hs
      rw [edist_nndist] at hs
      exact ENNReal.coe_lt_coe.mp hs
    exact (show r < dist a b from hn).le
  refine ⟨s,hsK,hsep,?_,fun x => actual_separated_local_refinement_count s r hr hsep x⟩
  intro x hx
  obtain ⟨a,ha,hxa⟩ := (isCover_maximalSeparatedSet hpfin) hx
  refine ⟨a,hSfin.mem_toFinset.mpr ha,?_⟩
  have hn : nndist x a ≤ d := edist_le_coe.mp hxa
  exact hn

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_separated_local_refinement_count
#print axioms GlobalEmbedding.Continuation.actual_exists_finite_bounded_refinement
