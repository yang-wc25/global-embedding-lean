import NormalPolar.JointSecondaryOriginalMixedData
import NormalPolar.JointSecondaryNativeCarrier
import NormalPolar.OriginalWaveSeedRefinement

/-! Actual original cutoffs supply the carrier fields of the manufactured
native secondary profiles. The whole open native domain is retained; the
background and prescribed supports map into their original closed carriers. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.Upgrade
open GlobalEmbedding.NormalPolar Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P P' Ep : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  [TopologicalSpace P'] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
local notation "Z" => EuclideanSpace ℝ (Fin 0)

theorem jointSecondary_original_primary_slice_support
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (p : P) (hpO : p ∈ Data.parameterOpen)
    (l : Fin Data.primaryCount) :
    tsupport (fun x : M => Data.cutoff l (p,x)) ⊆ jointSecondaryOriginalPrimaryCarrier Data p l := by
  intro x hx
  change (p,x) ∈ incrementsOriginalRelativeCutoffSupport Data l
  rw [parameterRound2_original_relativeSupport_eq Data hd.parameter_open]
  exact ⟨⟨hpO,mem_univ _⟩,tsupport_comp_subset_preimage (Data.cutoff l)
    (continuous_const.prodMk continuous_id) hx⟩

theorem jointSecondary_original_native_background_carrier
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (p : P) (hpO : p ∈ Data.parameterOpen)
    (B : OpenPartialHomeomorph P' Ep) (l : Fin Data.primaryCount) :
    incrementsGlobalRelativeSupport (round3ParameterNativeDomain B (univ : Set (P' × M)))
      (fun z : Ep × M => Data.cutoff l (p,z.2)) ⊆
      round3ParameterNativeDomain B ((univ : Set P') ×ˢ jointSecondaryOriginalPrimaryCarrier Data p l) := by
  intro z hz
  have hh := jointSecondary_native_spatial_cutoff_carrier B (fun x : M => Data.cutoff l (p,x)) hz
  exact ⟨hh.1,mem_univ _,jointSecondary_original_primary_slice_support Data hd p hpO l hh.2.2⟩

theorem jointSecondary_original_native_prescribed_piece_carrier
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (w : LocalLegalWave (n := m+1) F hF) (weight : ℝ)
    (refinement : OriginalWaveSeedRefinement F hF w weight)
    (B : OpenPartialHomeomorph P' Ep) (i : Fin refinement.count) :
    round3ParameterNativeDomain B
      ((fun z : P' × M => ((0 : Z),z.2)) ⁻¹' tsupport (refinement.cutoff i)) ⊆
      round3ParameterNativeDomain B ((univ : Set P') ×ˢ tsupport (w.cutoff : M → ℝ)) := by
  intro z hz
  exact ⟨hz.1,mem_univ _,(refinement.cutoff_support i hz.2).1⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondary_original_native_background_carrier
#print axioms GlobalEmbedding.Continuation.jointSecondary_original_native_prescribed_piece_carrier
