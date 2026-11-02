import OriginalIncrements.ExplicitPrimaryObserverProfilesAtScale
import CollarCompletion.PositivePrimaryLocalRefinementAtScale
import CompletionIntegration.PreparedPrimaryObserverCutoffs
import CollarCompletion.OriginalPrimaryPositiveProfiles
import CollarCompletion.PositivePrimaryRefinement
import OriginalCollars.WeightedCutoffCoordinateTransfer

/-!
# The exact weighted adapted cutoff profile at the current scale

All chart jets, original-observer scalar jets, and the chain rule use the
same current positive scale. The scalar and inverse weights cancel exactly;
no unweighted higher-order phase estimate enters the mean preparation.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation.OriginalIncrements
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

theorem original_primary_profiles_from_explicit_cutoff_bound_at_scale
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
    (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) (Packet : ℕ → ℝ)
    (hFinite : ∀ k, actualOriginalGivenInputProfile Data k ell ≠ ⊤)
    (hBudget : ∀ k, (actualOriginalGivenInputProfile Data k ell).toReal ≤ Packet k)
    (psi : P → ℝ) :
    let theta := fun i => sourceCollarNovParameterLocalized psi
      (round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
        (tensorLocalNormalizedCutoff RP.raw) i)
    ∀ (budgeted : OriginalBudgetedPrimarySupply Data theta)
      (profiles : Round3ParameterWholeReferenceProfiles Data hd hs theta budgeted.packet),
    let conditioned := budgeted.packet.replacePieces Data theta profiles.piece profiles.host profiles.cutoff
    let g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := Round3ParameterWholePrimaryIndex Data theta budgeted.packet)
      (fun p x => Data.F (p,x)) :=
      round3ParameterWholePrimaryFamily Data hd hs hn theta conditioned
    let Forward := originalBudgetedObserverForward Data theta budgeted Packet Parameter Spatial
    let Inverse := originalBudgetedObserverInverse Data theta budgeted Packet Parameter Spatial
    ∀ (Cutoff : ℕ → ℝ), (∀ k, 0 ≤ Cutoff k) →
    (∀ nu beta observer k z,
      parameterTensorModelEquiv (m+1) d z ∈ incrementsOriginalEvaluation Data.atlas Data.parameterChart
        Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet observer →
      ell^k*‖iteratedFDeriv ℝ k (fun y : X => g.eta nu beta
        ((Data.parameterChart observer.2).symm y.1,(Data.atlas.chart observer.1).symm y.2)) z‖ ≤ Cutoff k) →
    OriginalPrimaryPositiveChartProfilesAtScale Data g Forward Inverse
      (repairEntranceCompositionProfile Cutoff Inverse) ell := by
  intro theta budgeted profiles conditioned g Forward Inverse Cutoff hCutoff hOriginal
  have hPositive := original_budgeted_conditioned_positive_profiles_at_scale Data hd hs hn B hChart
    BS TS BP TP Ds Dp RS RP hSource hParameter Parameter Spatial hParameterNonneg hSpatialNonneg
    transition ell hell hell1 Packet hFinite hBudget psi budgeted profiles
  have hInverse : ∀ k, 0 ≤ Inverse k :=
    originalBudgetedObserverInverse_nonneg Data theta budgeted Packet Parameter Spatial
  intro nu beta i gN t etaN j z hz hPhysical
  have hActual := hPositive nu beta i j z hz hPhysical
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
  have hBound := OriginalCollars.actual_cutoff_coordinate_transfer_at_scale e a (gN.eta nu beta)
    Cutoff Inverse hCutoff hInverse hOriginalSmooth hTransition.2 ell hell j z hActual.1 (by
      intro k hk
      have h := hOriginal nu beta i k z hz
      have hFun : gN.eta nu beta ∘ e.symm = (fun y : X => g.eta nu beta
          ((Data.parameterChart i.2).symm y.1,(Data.atlas.chart i.1).symm y.2)) := by
        funext y
        rfl
      rw [hFun]
      exact h) (by
      intro k hk hkj
      exact (hPositive nu beta i k z hz hPhysical).2.2 hk |>.2)
  exact hBound

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_primary_profiles_from_explicit_cutoff_bound_at_scale
