import Repair.EntranceOriginalObserverJets
import Probes.Round3PreparedParameterSecondaryStableProfiles

/-! The actual stable secondary pieces inherit the numerical native chart
profiles through the literal two-sided parameter and spatial transition.
The original samples and the actual effective support pair are unchanged.
No compact maximum of observed chart derivatives is selected. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem increment_actual_secondary_observer_profiles
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3PreparedParameterSecondaryPacket Ref hd hs theta)
    (hSupport : ∀ i, tsupport (theta i) ⊆ (Ref.parameterChart i.2).source ×ˢ (univ : Set M))
    (NF NI Parameter Spatial : ℕ → ℝ)
    (hNF : ∀ j, 0 ≤ NF j) (hNI : ∀ j, 0 ≤ NI j)
    (hParameter : ∀ j, 0 ≤ Parameter j) (hSpatial : ∀ j, 0 ≤ Spatial j)
    (transition : RepairOriginalTransitionBudgets Ref Parameter Spatial)
    (hForward : ∀ r i a j z, z ∈ (packet.piece r i a).native.source →
      ‖iteratedFDeriv ℝ j (packet.piece r i a).native z‖ ≤ NF j)
    (hInverse : ∀ r i a j z, z ∈ (packet.piece r i a).native.target →
      ‖iteratedFDeriv ℝ j (packet.piece r i a).native.symm z‖ ≤ NI j)
    (hSamples : ∀ r i a z, z ∈ (packet.piece r i a).native.source →
      parameterTensorModelEquiv (m+1) d z ∈ incrementsOriginalEvaluation Ref.atlas Ref.parameterChart
        Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet i)
    (Bp Bs : ℝ)
    (hBp : ∀ ip z, z ∈ Ref.parameterNormDomain ip → ‖z‖ ≤ Bp)
    (hBs : ∀ ih z, z ∈ Ref.sourceNormDomain ih → ‖z‖ ≤ Bs) :
    ∀ (F : P → M → Ey) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p))
      (stable : ∀ r i (a : packet.s r i), Round3PreparedParameterStableSecondaryPiece Ref hd hs i r _ (packet.piece r i a) F hF)
      ell, 0 ≤ ell → ell ≤ 1 → ∀ r i (a : packet.s r i) observer,
      let choice := round3PreparedParameterSecondaryChoice Ref hd hs i r _ (stable r i a).piece
      let native := (choice.pullback (Ref.parameterChart observer.2)).toNative
      let t := ((OpenPartialHomeomorph.refl Ep).prod (Ref.atlas.chart observer.1)).symm.trans native.chart
      ∀ k z, parameterTensorModelEquiv (m+1) d z ∈ incrementsOriginalEvaluation Ref.atlas Ref.parameterChart
        Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet observer →
        ((Ref.parameterChart observer.2).symm z.1,(Ref.atlas.chart observer.1).symm z.2) ∈
          round3PreparedParameterSecondaryCarrier Ref r choice →
        z ∈ t.source ∧ t z ∈ t.target ∧
        ell^(k-1)*‖iteratedFDeriv ℝ k t z‖ ≤ repairEntranceOriginalForwardProfile Bp NF Parameter Spatial k ∧
        ell^(k-1)*‖iteratedFDeriv ℝ k t.symm (t z)‖ ≤ repairEntranceOriginalInverseProfile Bp Bs NI Parameter Spatial k := by
  intro F hF stable ell hell hell1 r i a observer choice native t k z hz hCarrierZ
  have hEqual := round3_prepared_parameter_secondary_stable_functions Ref hd hs i r _
    (packet.piece r i a) F hF (stable r i a) observer.2
  have hParent : tsupport choice.cutoff ⊆ tsupport (theta i) := by
    rw [hEqual.1]
    exact packet.parent r i a
  have hSource := (round3_prepared_parameter_secondary_carrier_source Ref hd hs i r (stable r i a).piece
    (theta i) (hSupport i) hParent).1
  have hNativeEval := (actual_original_native_evaluation_iff Ref hd observer z).mp hz
  have hp : z.1 ∈ (Ref.parameterChart observer.2).target := hd.parameter_norm_subset observer.2 hNativeEval.2.1
  have hx : z.2 ∈ (Ref.atlas.chart observer.1).target := hd.source_norm_subset observer.1 hNativeEval.1
  have hsrc : z ∈ t.source := by
    refine ⟨⟨mem_univ _,hx⟩,?_⟩
    apply (round3ParameterChartPullback_source_iff (Ref.parameterChart observer.2) choice.chart
      (round3_prepared_parameter_secondary_preserves Ref hd hs i r _ (stable r i a).piece)
      (z.1,(Ref.atlas.chart observer.1).symm z.2) hp).mpr
    exact hSource hCarrierZ
  let b := round3ParameterCrossNativeChart (Ref.parameterChart i.2)
    (Ref.parameterChart observer.2) (stable r i a).piece.native
  have hChart : native.chart = actualHostAdaptedChart (Ref.atlas.chart i.1) b :=
    (round3Parameter_cross_host_conjugation (Ref.parameterChart i.2)
      (Ref.parameterChart observer.2) (Ref.atlas.chart i.1) (stable r i a).piece.native
      (round3_prepared_signed_native_preserves_phase Ref hd hs i r _ (stable r i a).piece).1).symm
  have hNativeForw : ∀ j y, y ∈ (stable r i a).piece.native.source →
      ‖iteratedFDeriv ℝ j (stable r i a).piece.native y‖ ≤ NF j := by
    intro j y hy
    rw [(stable r i a).forward]
    exact hForward r i a j y ((stable r i a).source_subset hy)
  have hNativeInv : ∀ j y, y ∈ (stable r i a).piece.native.target →
      ‖iteratedFDeriv ℝ j (stable r i a).piece.native.symm y‖ ≤ NI j := by
    intro j y hy
    rw [(stable r i a).inverse]
    exact hInverse r i a j y ((stable r i a).target_subset hy)
  have hNativeSource : ∀ y ∈ (stable r i a).piece.native.source,
      y.1 ∈ Ref.parameterNormDomain i.2 ∧ y.2 ∈ Ref.sourceNormDomain i.1 := by
    intro y hy
    have hh := (actual_original_native_evaluation_iff Ref hd i y).mp
      (hSamples r i a y ((stable r i a).source_subset hy))
    exact ⟨hh.2.1,hh.1⟩
  have hj := repairEntrance_original_native_observer_jets Ref hd i.2 i.1 (stable r i a).piece.native
    _ (stable r i a).piece.slices (stable r i a).piece.data
    (round3_prepared_signed_native_preserves_phase Ref hd hs i r _ (stable r i a).piece).1
    NF NI Parameter Spatial hNF hNI hParameter hSpatial transition hNativeForw hNativeInv hNativeSource
    Bp Bs observer z hNativeEval.2.1 hNativeEval.1
    (hBp observer.2 z.1 hNativeEval.2.1) (hBs observer.1 z.2 hNativeEval.1)
  have ht : t = ((OpenPartialHomeomorph.refl Ep).prod (Ref.atlas.chart observer.1)).symm.trans
      (actualHostAdaptedChart (Ref.atlas.chart i.1) b) := by
    dsimp only [t]
    rw [hChart]
  have hj' := hj (ht ▸ hsrc) k
  rw [← ht] at hj'
  refine ⟨hsrc,t.map_source hsrc,?_,?_⟩
  · exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hell hell1)).trans hj'.1
  · exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hell hell1)).trans hj'.2

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.increment_actual_secondary_observer_profiles
