import CompletionIntegration.PreparedPrimaryObserverCutoffs
import CollarCompletion.OriginalPrimaryPositiveProfiles
import CollarCompletion.PositivePrimaryRefinement
import Repair.EntranceCutoffCoordinateTransfer

/-!
# The actual conditioned primary family supplies all required profiles

Both positive chart fields come from the actual native conditioning and the
literal original transition budgets. All original-observer cutoff derivatives
are manufactured from the actual physical compact cutoffs; the actual inverse
transition then supplies their adapted-coordinate derivatives. The original
Omega/Q and all physical fields remain unchanged. These are profiles of the
one actual packet, not a claim of original finite-budget class uniformity.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
open CollarCompletion
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem completion_original_primary_profiles
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (B : TensorBufferedChartFamily (Fin Data.parameterCount) P Ep)
    (hChart : B.chart = Data.parameterChart)
    (BS TS BP TP : ℕ → ℝ) (Ds Dp : ℕ)
    (RS : TensorRawCutoffPreparation Data.atlas BS TS Ds)
    (RP : TensorLocalRawPreparation B Data.parameterSet BP TP Dp)
    (hSource : ∀ i, bufferedSamplingCoordinates Data.atlas i ⊆ Data.sourceNormDomain i)
    (hParameter : ∀ i, tensorLocalSamplingCoordinates B i ⊆ Data.parameterNormDomain i)
    (Parameter Spatial : ℕ → ℝ)
    (hParameterNonneg : ∀ k, 0 ≤ Parameter k) (hSpatialNonneg : ∀ k, 0 ≤ Spatial k)
    (transition : RepairOriginalTransitionBudgets Data Parameter Spatial)
    (psi : P → ℝ) :
    let theta := fun i => sourceCollarNovParameterLocalized psi
      (round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
        (tensorLocalNormalizedCutoff RP.raw) i)
    ∀ (packet : Round3ParameterWholePrimaryPieceSupply Data theta)
      (profiles : Round3ParameterWholeReferenceProfiles Data hd hs theta packet),
    let conditioned := packet.replacePieces Data theta profiles.piece profiles.host profiles.cutoff
    let g := round3ParameterWholePrimaryFamily Data hd hs hn theta conditioned
    ∃ Forward Inverse Meta : ℕ → ℝ,
      (∀ k, 0 ≤ Forward k) ∧ (∀ k, 0 ≤ Inverse k) ∧ (∀ k, 0 ≤ Meta k) ∧
      OriginalPrimaryPositiveChartProfiles Data g Forward Inverse Meta := by
  intro theta packet profiles conditioned g
  obtain ⟨Forward,Inverse,hForward,hInverse,hPositive⟩ :=
    original_primary_conditioned_positive_profiles Data hd hs hn B hChart BS TS BP TP Ds Dp
      RS RP hSource hParameter Parameter Spatial hParameterNonneg hSpatialNonneg transition
      psi packet profiles
  have hSupport : ∀ i, tsupport (theta i) ⊆
      (Data.parameterChart i.2).source ×ˢ Data.atlas.inner i.1 := by
    intro i z hz
    have h := original_parameter_localized_parent_inner Data.atlas B Data.parameterSet
      BS TS BP TP Ds Dp RS RP psi i hz
    have hp := B.inner_subset i.2 h.1
    rw [hChart] at hp
    exact ⟨hp,h.2⟩
  obtain ⟨Cutoff,hCutoff,hOriginal⟩ := prepared_primary_original_observer_cutoff_profiles
    Data hd hs hn theta conditioned hSupport Parameter Spatial hParameterNonneg hSpatialNonneg transition
  let Meta := repairEntranceCompositionProfile Cutoff Inverse
  have hMeta : ∀ k, 0 ≤ Meta k :=
    repairEntranceCompositionProfile_nonneg Cutoff Inverse hCutoff hInverse
  refine ⟨Forward,Inverse,Meta,hForward,hInverse,hMeta,?_⟩
  intro ell hell hell1 nu beta i gN t etaN j z hz hPhysical
  have hActual := hPositive ell hell hell1 nu beta i j z hz hPhysical
  refine ⟨hActual.1,hActual.2.1,hActual.2.2,?_⟩
  let Bobs := Data.parameterChart i.2
  let e := (OpenPartialHomeomorph.refl Ep).prod (Data.atlas.chart i.1)
  let a := gN.chart nu beta
  have hChart := round3ParameterLiftedPrimaryChart_smooth Data hd beta.1.2 nu _
    (round3ParameterWholePrimaryPiece Data hd theta conditioned nu beta)
  have hNative := round3ParameterChartPullback_smooth Bobs (hd.parameter_charts_smooth i.2)
    (g.chart nu beta) hChart.1 hChart.2
  have hTransition := round3Parameter_native_observer_transition_smooth a hNative.1 hNative.2
    (Data.atlas.chart i.1) (hd.atlas_smooth.chart_mem i.1)
  have hEta := (round3ParameterWholePrimaryFamily_cutoff_geometry Data hd hs hn theta
    conditioned nu beta).1
  have hParam (w : X) (hw : w ∈ t.source) : w.1 ∈ Bobs.target :=
    ((round3ParameterChartPullback_source Bobs (g.chart nu beta) (e.symm w)).mp hw.2).1
  have hOriginalSmooth : ContDiffOn ℝ ∞ (gN.eta nu beta ∘ e.symm) t.source := by
    have hB : ContMDiffOn 𝓘(ℝ,X) 𝓘(ℝ,Ep) ∞ (fun w : X => Bobs.symm w.1) t.source :=
      (contMDiffOn_symm_of_mem_maximalAtlas (hd.parameter_charts_smooth i.2)).comp
        contDiff_fst.contMDiff.contMDiffOn hParam
    have hA : ContMDiffOn 𝓘(ℝ,X) 𝓙 ∞
        (fun w : X => (Data.atlas.chart i.1).symm w.2) t.source :=
      (contMDiffOn_symm_of_mem_maximalAtlas (hd.atlas_smooth.chart_mem i.1)).comp
        contDiff_snd.contMDiff.contMDiffOn (fun _ hw => hw.1.2)
    exact (hEta.comp_contMDiffOn (hB.prodMk hA)).contDiffOn
  have hBound := repairEntrance_actual_cutoff_coordinate_transfer e a (gN.eta nu beta)
    Cutoff Inverse hCutoff hInverse hOriginalSmooth hTransition.2 j z hActual.1 (by
      intro k hk
      have h := hOriginal 1 zero_le_one le_rfl nu beta i k z hz
      have hFun : gN.eta nu beta ∘ e.symm = (fun y : X => g.eta nu beta
          ((Data.parameterChart i.2).symm y.1,(Data.atlas.chart i.1).symm y.2)) := by
        funext y
        rfl
      rw [hFun]
      simpa only [one_pow,one_mul] using h) (by
      intro k hk hkj
      have h := (hPositive 1 zero_le_one le_rfl nu beta i k z hz hPhysical).2.2 hk
      simpa only [one_pow,one_mul] using h.2)
  exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hell hell1)).trans hBound

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.completion_original_primary_profiles
