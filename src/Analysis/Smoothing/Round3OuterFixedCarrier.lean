import Probes.Round3ParameterOriginalPrimaryGeometry
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! A fixed, explicit carrier for an actual finite ordinary partition.
The scalar plateau is chosen from the original cutoffs, before any later
smoothed map or scale. Its support stays inside the union where an ORIGINAL
cutoff is nonzero. Multiplying every cutoff by this one plateau preserves
the original germ partition and never increases its overlap count. -/

noncomputable section
open Set Function Manifold Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {E H X A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace X] [ChartedSpace H X] [Fintype A]

def round3FixedCarrierSum (eta : A → X → ℝ) (z : X) : ℝ := ∑ a, eta a z

def round3FixedCarrierPlateau (eta : A → X → ℝ) (z : X) : ℝ :=
  Real.smoothTransition (4 * (round3FixedCarrierSum eta z)^2 - 1)

def round3FixedCarrierDomain (eta : A → X → ℝ) : Set X :=
  {z | (1/8 : ℝ) < (round3FixedCarrierSum eta z)^2}

def round3FixedCarrierCutoff (eta : A → X → ℝ) (a : A) (z : X) : ℝ :=
  round3FixedCarrierPlateau eta z * eta a z

structure Round3FixedCarrierProperties (eta : A → X → ℝ) (K : Set X) (R : ℕ) : Prop where
  open_domain : IsOpen (round3FixedCarrierDomain eta)
  covers : K ⊆ round3FixedCarrierDomain eta
  active : ∀ z ∈ round3FixedCarrierDomain eta, ∃ a, eta a z ≠ 0
  smooth : ∀ a, ContMDiff I 𝓘(ℝ,ℝ) ∞ (round3FixedCarrierCutoff eta a)
  compact : ∀ a, IsCompact (tsupport (round3FixedCarrierCutoff eta a))
  support : ∀ a, tsupport (round3FixedCarrierCutoff eta a) ⊆
    tsupport (eta a) ∩ round3FixedCarrierDomain eta
  partition : ∀ z ∈ K, ∀ᶠ w in 𝓝 z, ∑ a, round3FixedCarrierCutoff eta a w = 1
  count : ∀ z, (Finset.univ.filter (fun a => z ∈ tsupport (round3FixedCarrierCutoff eta a))).card ≤ R

theorem round3_fixed_cutoff_carrier
    (eta : A → X → ℝ) (K : Set X) (R : ℕ)
    (hSmooth : ∀ a, ContMDiff I 𝓘(ℝ,ℝ) ∞ (eta a))
    (hCompact : ∀ a, IsCompact (tsupport (eta a)))
    (hPartition : ∀ z ∈ K, ∀ᶠ w in 𝓝 z, ∑ a, eta a w = 1)
    (hCount : ∀ z, (Finset.univ.filter (fun a => z ∈ tsupport (eta a))).card ≤ R) :
    Round3FixedCarrierProperties (I := I) eta K R := by
  have hSum : ContMDiff I 𝓘(ℝ,ℝ) ∞ (round3FixedCarrierSum eta) :=
    contMDiff_finsetSum (fun a _ => hSmooth a)
  have hSquare : ContMDiff I 𝓘(ℝ,ℝ) ∞ (fun z => (round3FixedCarrierSum eta z)^2) :=
    hSum.pow 2
  have hPlateau : ContMDiff I 𝓘(ℝ,ℝ) ∞ (round3FixedCarrierPlateau eta) :=
    (Real.smoothTransition.contDiff.contMDiff).comp
      ((contMDiff_const.mul hSquare).sub contMDiff_const)
  have hSupport : tsupport (round3FixedCarrierPlateau eta) ⊆
      {z | (1/4 : ℝ) ≤ (round3FixedCarrierSum eta z)^2} := by
    apply closure_minimal
    · intro z hz
      have hn : round3FixedCarrierPlateau eta z ≠ 0 := hz
      have hp : 0 < 4 * (round3FixedCarrierSum eta z)^2 - 1 := by
        exact lt_of_not_ge (fun h => hn (Real.smoothTransition.zero_of_nonpos h))
      change (1/4 : ℝ) ≤ (round3FixedCarrierSum eta z)^2
      linarith
    · exact isClosed_le continuous_const hSquare.continuous
  have hSupportDomain : tsupport (round3FixedCarrierPlateau eta) ⊆ round3FixedCarrierDomain eta := by
    intro z hz
    have h := hSupport hz
    change (1/4 : ℝ) ≤ (round3FixedCarrierSum eta z)^2 at h
    change (1/8 : ℝ) < (round3FixedCarrierSum eta z)^2
    linarith
  have hNewSupport (a : A) : tsupport (round3FixedCarrierCutoff eta a) ⊆
      tsupport (eta a) ∩ round3FixedCarrierDomain eta := by
    intro z hz
    exact ⟨tsupport_mul_subset_right hz,hSupportDomain (tsupport_mul_subset_left hz)⟩
  refine {
    open_domain := isOpen_lt continuous_const hSquare.continuous
    covers := ?_
    active := ?_
    smooth := fun a => hPlateau.mul (hSmooth a)
    compact := fun a => (hCompact a).of_isClosed_subset (isClosed_tsupport _) (fun _ h => (hNewSupport a h).1)
    support := hNewSupport
    partition := ?_
    count := ?_ }
  · intro z hz
    have h : round3FixedCarrierSum eta z = 1 := (hPartition z hz).self_of_nhds
    change (1/8 : ℝ) < (round3FixedCarrierSum eta z)^2
    rw [h]
    norm_num
  · intro z hz
    by_contra h
    push_neg at h
    have hs : round3FixedCarrierSum eta z = 0 := by simp [round3FixedCarrierSum,h]
    change (1/8 : ℝ) < (round3FixedCarrierSum eta z)^2 at hz
    rw [hs] at hz
    norm_num at hz
  · intro z hz
    filter_upwards [hPartition z hz] with w hw
    change ∑ a, round3FixedCarrierPlateau eta w * eta a w = 1
    rw [← Finset.mul_sum,hw]
    have hs : round3FixedCarrierSum eta w = 1 := hw
    simp only [round3FixedCarrierPlateau,hs]
    rw [Real.smoothTransition.one_of_one_le (by norm_num)]
    norm_num
  · intro z
    apply le_trans (Finset.card_le_card ?_) (hCount z)
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hNewSupport a (Finset.mem_filter.mp ha).2).1⟩

#print axioms round3_fixed_cutoff_carrier
end GlobalEmbedding.Continuation
