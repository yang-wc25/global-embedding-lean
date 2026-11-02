import OriginalIncrements.OriginalBudgetedNativeJets
import OriginalIncrements.OriginalPhysicalPhaseJets
import CollarCompletion.OriginalParentSampling
import CompletionIntegration.PointwiseObserverJets
import Probes.Round3ParameterWholeReferenceProfiles
import Probes.Round3ParameterWholePieceReplacement

/-!
# Explicit original-input positive profiles for the actual conditioned packet

Reference conditioning retains the exact native forward/inverse functions
and physical cutoffs of the budgeted packet. The original sampled phase
jets therefore bound the actual conditioned observer maps. These named
profiles replace the opaque compact derivative maxima in the mean supplier;
their j-th entries read only original Given through j-1 and positive
transition derivatives through j. Finite maxima have no cardinal multiplier.
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

def originalBudgetedObserverForward
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (budgeted : OriginalBudgetedPrimarySupply Data theta)
    (Packet Parameter Spatial : ℕ → ℝ) (k : ℕ) : ℝ :=
  round3PreparedFiniteMaximum (fun a : Fin Data.primaryCount ×
      (Fin Data.atlas.count × Fin Data.parameterCount) =>
    phaseObserverForwardBudget (budgeted.mu a.1 a.2) (budgeted.Mb a.1 a.2)
      (phaseFromGivenBudget m d Packet) Parameter Spatial k)

def originalBudgetedObserverInverse
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (budgeted : OriginalBudgetedPrimarySupply Data theta)
    (Packet Parameter Spatial : ℕ → ℝ) (k : ℕ) : ℝ :=
  round3PreparedFiniteMaximum (fun a : Fin Data.primaryCount ×
      (Fin Data.atlas.count × Fin Data.parameterCount) =>
    phaseObserverInverseBudget (budgeted.mu a.1 a.2) (budgeted.Mb a.1 a.2)
      (phaseFromGivenBudget m d Packet) Parameter Spatial k)

omit [IsManifold 𝓘(ℝ,D) ∞ M] [BoundarylessManifold 𝓘(ℝ,D) M] [IsManifold 𝓘(ℝ,Ep) ∞ P] in
theorem originalBudgetedObserverForward_nonneg
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (budgeted : OriginalBudgetedPrimarySupply Data theta)
    (Packet Parameter Spatial : ℕ → ℝ) (k : ℕ) :
    0 ≤ originalBudgetedObserverForward Data theta budgeted Packet Parameter Spatial k :=
  round3PreparedFiniteMaximum_nonneg _

omit [IsManifold 𝓘(ℝ,D) ∞ M] [BoundarylessManifold 𝓘(ℝ,D) M] [IsManifold 𝓘(ℝ,Ep) ∞ P] in
theorem originalBudgetedObserverInverse_nonneg
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (budgeted : OriginalBudgetedPrimarySupply Data theta)
    (Packet Parameter Spatial : ℕ → ℝ) (k : ℕ) :
    0 ≤ originalBudgetedObserverInverse Data theta budgeted Packet Parameter Spatial k :=
  round3PreparedFiniteMaximum_nonneg _

omit [IsManifold 𝓘(ℝ,D) ∞ M] [BoundarylessManifold 𝓘(ℝ,D) M]
  [ChartedSpace Ep P] [IsManifold 𝓘(ℝ,Ep) ∞ P] in
theorem original_lifted_primary_source_geometry
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (ip : Fin Data.parameterCount) (nu : Fin Data.primaryCount) (W : Set (Ep × M))
    (piece : Round3PreparedPrimaryPiece Data ip nu W) (z : P × M)
    (hz : z ∈ (round3ParameterLiftedPrimaryChart Data ip nu W piece).source) :
    z.1 ∈ (Data.parameterChart ip).source ∧ z.2 ∈ (Data.atlas.chart piece.host).source ∧
    ((Data.parameterChart ip) z.1,(Data.atlas.chart piece.host) z.2) ∈ piece.native.source ∧
    z ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data := by
  have h := (round3ParameterChartPullback_source (Data.parameterChart ip).symm
    (actualHostAdaptedChart (Data.atlas.chart piece.host) piece.native) z).mp hz
  have ha := piece.active ((Data.parameterChart ip) z.1,z.2) h.2.1
  refine ⟨h.1,h.2.1.1.2,h.2.1.2,?_⟩
  simpa only [(Data.parameterChart ip).left_inv h.1] using ha

theorem original_budgeted_conditioned_positive_profiles
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
    (Packet : ℕ → ℝ)
    (hFinite : ∀ k, actualOriginalGivenInputProfile Data k 1 ≠ ⊤)
    (hBudget : ∀ k, (actualOriginalGivenInputProfile Data k 1).toReal ≤ Packet k)
    (psi : P → ℝ) :
    let theta := fun i => sourceCollarNovParameterLocalized psi
      (round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
        (tensorLocalNormalizedCutoff RP.raw) i)
    ∀ (budgeted : OriginalBudgetedPrimarySupply Data theta),
    ∀ (profiles : Round3ParameterWholeReferenceProfiles Data hd hs theta budgeted.packet),
    let conditioned := budgeted.packet.replacePieces Data theta profiles.piece profiles.host profiles.cutoff
    let g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := Round3ParameterWholePrimaryIndex Data theta budgeted.packet)
      (fun p x => Data.F (p,x)) :=
      round3ParameterWholePrimaryFamily Data hd hs hn theta conditioned
    let Forward := originalBudgetedObserverForward Data theta budgeted Packet Parameter Spatial
    let Inverse := originalBudgetedObserverInverse Data theta budgeted Packet Parameter Spatial
    ∀ ell, 0 ≤ ell → ell ≤ 1 → ∀ (nu : Fin Data.primaryCount)
      (beta : Round3ParameterWholePrimaryIndex Data theta budgeted.packet)
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
  intro theta budgeted profiles conditioned g Forward Inverse
  let packet := budgeted.packet
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
      exact round3PreparedPrimarySigmaPiece_active Data hd i
        ((Data.parameterChart i.2).target ×ˢ (univ : Set M))
        (fun mu => ↥(budgeted.packet.s mu i)) (fun mu b => profiles.piece mu i b) nu a
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
    let physical : P × M := ((Data.parameterChart observer.2).symm z.1,
      (Data.atlas.chart observer.1).symm z.2)
    let point := incrementsCompletionOriginalHostPoint Data i.2 i.1 observer z
    have hLifted : g.eta nu ⟨i,nu,a⟩ = round3ParameterLiftedPrimaryCutoff Data i.2 nu _ piece := by
      exact (round3ParameterWholePrimaryFamily_eta Data hd hs hn theta conditioned nu ⟨i,nu,a⟩).trans
        (congrArg (round3ParameterLiftedPrimaryCutoff Data i.2 nu _) hPiece)
    have hEtaOld : physical ∈ tsupport (round3ParameterLiftedPrimaryCutoff Data i.2 nu _
        (packet.piece nu i a)) := by
      rw [hLifted] at hEta
      rwa [round3Parameter_lifted_cutoff_eq_of_native_eq Data i.2 nu _
        (packet.piece nu i a) piece (profiles.cutoff nu i a)] at hEta
    have hOld := original_lifted_primary_source_geometry Data i.2 nu _ (packet.piece nu i a)
      physical (packet.source nu i a hEtaOld)
    have hPointSource : point ∈ (packet.piece nu i a).native.source := by
      simpa only [packet.host nu i a,point,physical,incrementsCompletionOriginalHostPoint] using hOld.2.2.1
    have hOwnSample : parameterTensorModelEquiv (m+1) d point ∈
        incrementsOriginalPrimaryEvaluation Data nu i := by
      refine ⟨(actual_original_native_evaluation_iff Data hd i point).mpr ?_,?_⟩
      · refine ⟨hOwn.2,hOwn.1,?_⟩
        change (Data.parameterChart i.2).symm ((Data.parameterChart i.2) physical.1) ∈ Data.parameterSet
        rw [(Data.parameterChart i.2).left_inv hOld.1]
        exact hEvaluation.2.2
      · change incrementsOriginalJointPoint Data.atlas Data.parameterChart i
          (parameterTensorModelEquiv (m+1) d point) ∈ Data.primaryDomain nu
        rw [actual_original_jointPoint_native]
        change ((Data.parameterChart i.2).symm ((Data.parameterChart i.2) physical.1),
          (Data.atlas.chart i.1).symm ((Data.atlas.chart i.1) physical.2)) ∈ Data.primaryDomain nu
        rw [(Data.parameterChart i.2).left_inv hOld.1,
          (Data.atlas.chart i.1).left_inv (by simpa only [packet.host nu i a] using hOld.2.1)]
        exact hOld.2.2.2.1
    let Phase := phaseFromGivenBudget m d Packet
    let F := phaseForwardBudget (budgeted.Mb nu i) Phase
    let I := phaseInverseBudget (budgeted.mu nu i) (budgeted.Mb nu i) Phase
    have hNative := original_budgeted_native_positive_jets_at Data hd hs theta budgeted nu i a point
      hPointSource hOwnSample Packet 1 zero_lt_one k (fun r _ => hFinite r) (fun r _ => hBudget r)
    have hNativeCond (r : ℕ) (hr : 1 ≤ r) (hrk : r ≤ k) :
        1^(r-1)*‖iteratedFDeriv ℝ r piece.native
          (incrementsCompletionOriginalHostPoint Data i.2 piece.host observer z)‖ ≤ F r ∧
        1^(r-1)*‖iteratedFDeriv ℝ r piece.native.symm
          (piece.native (incrementsCompletionOriginalHostPoint Data i.2 piece.host observer z))‖ ≤ I r := by
      have hh := hNative r hr hrk
      change 1^(r-1)*‖iteratedFDeriv ℝ r (profiles.piece nu i a).native _‖ ≤ _ ∧
        1^(r-1)*‖iteratedFDeriv ℝ r (profiles.piece nu i a).native.symm
          ((profiles.piece nu i a).native _)‖ ≤ _
      rw [profiles.forward nu i a,profiles.inverse nu i a,hHost]
      exact hh
    have hPoint := incrementsCompletion_original_native_observer_finite_weighted_jets_at
      Data hd i.2 piece.host piece.native
      (fun y : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm y.1,y.2))
      piece.slices piece.data hPreserves F I Parameter Spatial
      (fun r _ => phaseForwardBudget_nonneg _ (budgeted.Mb_nonneg nu i) Phase
        (fun r _ => phaseFromGivenBudget_nonneg m d Packet r) r)
      (fun r _ => phaseInverseBudget_nonneg _ _ (budgeted.mu_pos nu i) (budgeted.Mb_nonneg nu i) Phase
        (fun r _ => phaseFromGivenBudget_nonneg m d Packet r) r)
      (fun r _ => hParameterNonneg r) (fun r _ => hSpatialNonneg r) transition
      1 zero_lt_one le_rfl observer z hEvaluation.2.1 hEvaluation.1 hOwn.1 hOwnX k hk
      (fun r hr hrk => (hNativeCond r hr hrk).1)
      (fun r hr hrk => (hNativeCond r hr hrk).2)
    have hOriginalT : t = ((OpenPartialHomeomorph.refl Ep).prod (Data.atlas.chart observer.1)).symm.trans
        (actualHostAdaptedChart (Data.atlas.chart piece.host)
          (round3ParameterCrossNativeChart (Data.parameterChart i.2)
            (Data.parameterChart observer.2) piece.native)) := by
      dsimp only [t]
      rw [hActualChart]
    have hPointAt := hPoint (hOriginalT ▸ hTSource)
    rw [← hOriginalT] at hPointAt
    have hWeight : ell^(k-1) ≤ 1 := pow_le_one₀ hell hell1
    have hFor : ‖iteratedFDeriv ℝ k t z‖ ≤
        phaseObserverForwardBudget (budgeted.mu nu i) (budgeted.Mb nu i) Phase Parameter Spatial k := by
      simpa only [one_pow,one_mul,phaseObserverForwardBudget,F] using hPointAt.1
    have hInv : ‖iteratedFDeriv ℝ k t.symm (t z)‖ ≤
        phaseObserverInverseBudget (budgeted.mu nu i) (budgeted.Mb nu i) Phase Parameter Spatial k := by
      simpa only [one_pow,one_mul,phaseObserverInverseBudget,I] using hPointAt.2
    exact ⟨((mul_le_of_le_one_left (norm_nonneg _) hWeight).trans hFor).trans
      (round3PreparedFiniteMaximum_bound
        (fun a : Fin Data.primaryCount × (Fin Data.atlas.count × Fin Data.parameterCount) =>
          phaseObserverForwardBudget (budgeted.mu a.1 a.2) (budgeted.Mb a.1 a.2)
            Phase Parameter Spatial k) (nu,i)),
      ((mul_le_of_le_one_left (norm_nonneg _) hWeight).trans hInv).trans
      (round3PreparedFiniteMaximum_bound
        (fun a : Fin Data.primaryCount × (Fin Data.atlas.count × Fin Data.parameterCount) =>
          phaseObserverInverseBudget (budgeted.mu a.1 a.2) (budgeted.Mb a.1 a.2)
            Phase Parameter Spatial k) (nu,i))⟩
  · intro observer gN t k z hz hEta
    have hZero : g.eta nu ⟨i,mu,a⟩ = 0 := by
      change (round3ParameterWholePrimaryFamily Data hd hs hn theta conditioned).eta nu ⟨i,mu,a⟩ = 0
      rw [round3ParameterWholePrimaryFamily_eta]
      simp only [round3ParameterWholePrimaryPiece,round3PreparedPrimarySigmaPiece,hmu,dite_false,
        round3ParameterLiftedPrimaryCutoff_empty]
    rw [hZero,tsupport_zero] at hEta
    exact hEta.elim

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_budgeted_conditioned_positive_profiles
