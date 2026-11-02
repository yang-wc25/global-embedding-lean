import CollarCompletion.OriginalParentSampling
import CompletionIntegration.PointwiseObserverJets
import Probes.Round3ParameterWholeReferenceProfiles
import Probes.Round3ParameterWholePieceReplacement

/-!
# Actual conditioned primary profiles on the original samples

The genuine reference conditioning already supplies native chart profiles.
Its replacement packet retains the same physical cutoffs and parent supports.
Those supports put the actual owner point in the original Q/Omega, so the
pointwise transition estimate supplies every positive observer chart jet.
The two resulting profiles are fixed before ell. No compactness of an
original sampling set and no zeroth-order observer-coordinate bound is used.

This module supplies only the forward/inverse chart fields. It does not
assume the cutoff-jet conclusion or claim that the qualitative reference
conditioning is a uniform finite-budget entrance for the original theorem.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation.CollarCompletion

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

theorem original_primary_conditioned_positive_profiles
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
    let g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := Round3ParameterWholePrimaryIndex Data theta packet)
      (fun p x => Data.F (p,x)) :=
      round3ParameterWholePrimaryFamily Data hd hs hn theta conditioned
    ∃ Forward Inverse : ℕ → ℝ, (∀ k, 0 ≤ Forward k) ∧ (∀ k, 0 ≤ Inverse k) ∧
      ∀ ell, 0 ≤ ell → ell ≤ 1 → ∀ (nu : Fin Data.primaryCount)
      (beta : Round3ParameterWholePrimaryIndex Data theta packet)
      (observer : Fin Data.atlas.count × Fin Data.parameterCount),
      let gN := round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart observer.2)
      let t := ((OpenPartialHomeomorph.refl Ep).prod (Data.atlas.chart observer.1)).symm.trans
        (gN.chart nu beta)
      ∀ k z, parameterTensorModelEquiv (m+1) d z ∈
        incrementsOriginalEvaluation Data.atlas Data.parameterChart
          Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet observer →
        ((Data.parameterChart observer.2).symm z.1,(Data.atlas.chart observer.1).symm z.2) ∈
          tsupport (g.eta nu beta) →
        z ∈ t.source ∧ t z ∈ t.target ∧
        (1 ≤ k → ell^(k-1)*‖iteratedFDeriv ℝ k t z‖ ≤ Forward k ∧
          ell^(k-1)*‖iteratedFDeriv ℝ k t.symm (t z)‖ ≤ Inverse k) := by
  intro theta packet profiles conditioned g
  let Forward := repairEntranceCompositionProfile
    (repairEntranceConjugatedForwardProfile profiles.Tforward Parameter Parameter) Spatial
  let Inverse := repairEntranceCompositionProfile Spatial
    (repairEntranceConjugatedForwardProfile profiles.Tinv Parameter Parameter)
  have hCF : ∀ k, 0 ≤ repairEntranceConjugatedForwardProfile profiles.Tforward Parameter Parameter k :=
    repairEntranceCompositionProfile_nonneg Parameter
      (repairEntranceCompositionProfile profiles.Tforward Parameter)
      hParameterNonneg
      (repairEntranceCompositionProfile_nonneg profiles.Tforward Parameter
        profiles.Tforward_nonneg hParameterNonneg)
  have hCI : ∀ k, 0 ≤ repairEntranceConjugatedForwardProfile profiles.Tinv Parameter Parameter k :=
    repairEntranceCompositionProfile_nonneg Parameter
      (repairEntranceCompositionProfile profiles.Tinv Parameter)
      hParameterNonneg
      (repairEntranceCompositionProfile_nonneg profiles.Tinv Parameter
        profiles.Tinv_nonneg hParameterNonneg)
  refine ⟨Forward,Inverse,
    repairEntranceCompositionProfile_nonneg _ Spatial hCF hSpatialNonneg,
    repairEntranceCompositionProfile_nonneg Spatial _ hSpatialNonneg hCI,?_⟩
  intro ell hell hell1 nu beta
  rcases beta with ⟨i,mu,a⟩
  by_cases hmu : mu = nu
  · subst mu
    intro observer gN t k z hz hEta
    have hEvaluation := (actual_original_native_evaluation_iff Data hd observer z).mp hz
    have hpTarget : z.1 ∈ (Data.parameterChart observer.2).target :=
      hd.parameter_norm_subset observer.2 hEvaluation.2.1
    have hxTarget : z.2 ∈ (Data.atlas.chart observer.1).target :=
      hd.source_norm_subset observer.1 hEvaluation.1
    have hGeometry := round3ParameterWholePrimaryFamily_cutoff_geometry
      Data hd hs hn theta conditioned nu ⟨i,nu,a⟩
    have hPhysicalParent := hGeometry.2.2.1 hEta
    have hOwn := original_parameter_localized_parent_original_samples Data B hChart
      BS TS BP TP Ds Dp RS RP hSource hParameter psi i observer z hPhysicalParent
    have hPhysicalSource := hGeometry.2.2.2 hEta
    have hGPreserves : Round3ParameterChartPreserves (g.chart nu ⟨i,nu,a⟩) :=
      round3ParameterLiftedPrimaryChart_preserves Data i.2 nu _
        (round3ParameterWholePrimaryPiece Data hd theta conditioned nu ⟨i,nu,a⟩)
    have hNativeSource : (z.1,(Data.atlas.chart observer.1).symm z.2) ∈
        (gN.chart nu ⟨i,nu,a⟩).source := by
      change _ ∈ (round3ParameterChartPullback (Data.parameterChart observer.2)
        (g.chart nu ⟨i,nu,a⟩)).source
      exact (round3ParameterChartPullback_source_iff (Data.parameterChart observer.2)
        (g.chart nu ⟨i,nu,a⟩) hGPreserves
        (z.1,(Data.atlas.chart observer.1).symm z.2) hpTarget).mpr hPhysicalSource
    have hTSource : z ∈ t.source := ⟨⟨mem_univ _,hxTarget⟩,hNativeSource⟩
    refine ⟨hTSource,t.map_source hTSource,?_⟩
    intro hk
    let piece := profiles.piece nu i a
    have hPiece : round3ParameterWholePrimaryPiece Data hd theta conditioned nu ⟨i,nu,a⟩ = piece := by
      simp only [round3ParameterWholePrimaryPiece,round3PreparedPrimarySigmaPiece_active] <;> rfl
    have hHost : piece.host = i.1 := (profiles.host nu i a).trans (packet.host nu i a)
    have hPreserves : Round3ParameterChartPreserves piece.native :=
      (round3Parameter_primary_native_preserves_phase Data hd i.2 nu _ piece).1
    have hActualChart : gN.chart nu ⟨i,nu,a⟩ =
        actualHostAdaptedChart (Data.atlas.chart piece.host)
          (round3ParameterCrossNativeChart (Data.parameterChart i.2)
            (Data.parameterChart observer.2) piece.native) := by
      change round3ParameterChartPullback (Data.parameterChart observer.2)
        (round3ParameterLiftedPrimaryChart Data i.2 nu _
          (round3ParameterWholePrimaryPiece Data hd theta conditioned nu ⟨i,nu,a⟩)) = _
      rw [hPiece]
      exact (round3Parameter_cross_host_conjugation (Data.parameterChart i.2)
        (Data.parameterChart observer.2) (Data.atlas.chart piece.host) piece.native hPreserves).symm
    have hOwnX : Data.atlas.chart piece.host ((Data.atlas.chart observer.1).symm z.2) ∈
        Data.sourceNormDomain piece.host := by
      rw [hHost]
      exact hOwn.2
    have hPoint := completion_original_native_observer_positive_jets_at Data hd i.2 piece.host
      piece.native (fun y : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm y.1,y.2))
      piece.slices piece.data hPreserves profiles.Tforward profiles.Tinv Parameter Spatial
      profiles.Tforward_nonneg profiles.Tinv_nonneg hParameterNonneg hSpatialNonneg transition
      (profiles.forward_jets nu i a) (profiles.inverse_jets nu i a)
      observer z hEvaluation.2.1 hEvaluation.1 hOwn.1 hOwnX
    have hOriginalT : t = ((OpenPartialHomeomorph.refl Ep).prod (Data.atlas.chart observer.1)).symm.trans
        (actualHostAdaptedChart (Data.atlas.chart piece.host)
          (round3ParameterCrossNativeChart (Data.parameterChart i.2)
            (Data.parameterChart observer.2) piece.native)) := by
      dsimp only [t]
      rw [hActualChart]
    have hPointAt := hPoint (hOriginalT ▸ hTSource) k hk
    rw [← hOriginalT] at hPointAt
    have hWeight : ell^(k-1) ≤ 1 := pow_le_one₀ hell hell1
    exact ⟨(mul_le_of_le_one_left (norm_nonneg _) hWeight).trans hPointAt.1,
      (mul_le_of_le_one_left (norm_nonneg _) hWeight).trans hPointAt.2⟩
  · intro observer gN t k z hz hEta
    have hZero : g.eta nu ⟨i,mu,a⟩ = 0 := by
      change (round3ParameterWholePrimaryFamily Data hd hs hn theta conditioned).eta nu ⟨i,mu,a⟩ = 0
      rw [round3ParameterWholePrimaryFamily_eta]
      simp only [round3ParameterWholePrimaryPiece,round3PreparedPrimarySigmaPiece,hmu,dite_false,
        round3ParameterLiftedPrimaryCutoff_empty]
    rw [hZero,tsupport_zero] at hEta
    exact hEta.elim

end GlobalEmbedding.Continuation.CollarCompletion
#print axioms GlobalEmbedding.Continuation.CollarCompletion.original_primary_conditioned_positive_profiles
