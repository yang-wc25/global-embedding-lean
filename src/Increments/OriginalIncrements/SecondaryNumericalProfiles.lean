import Repair.IncrementSecondaryChartBudget
import IncrementsCompletion.PositiveSecondaryPacketProfiles

/-!
# Numerical secondary budgets enter the actual completion profiles

The same signed packet supplies its numerical chart bounds and its literal
refinement cutoff. This bridge uses these bounds directly; it chooses no
compact derivative maximum and introduces no total packet cardinal factor.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Filter Manifold IsManifold
open scoped ContDiff Topology Classical BigOperators
namespace GlobalEmbedding.Continuation.OriginalIncrements

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "Z" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
private local instance : ChartedSpace (Ep × D) (P × M) := prodChartedSpace Ep P D M
private local instance : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓙) (n := ∞) P M

private theorem originalSecondaryCutoffPrefix_bound (P : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j)
    {k j : ℕ} (hkj : k ≤ j) : P k ≤ bufferedTransitionPrefix P j := by
  have h := Finset.single_le_sum (fun l (_ : l ∈ Finset.range (j+1)) => hP l)
    (show k ∈ Finset.range (j+1) by simp; omega)
  exact h.trans (by unfold bufferedTransitionPrefix; linarith)

/-- The literal numerical chart budget gives the positive observer jets
of the reference packet itself, without a stability restriction or a new
profile selected by compactness. -/
theorem original_secondary_numerical_positive_profiles
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (packet : Round3PreparedParameterSecondaryPacket Data hd hs theta)
    (budget : IncrementSecondaryChartBudget Data hd hs theta packet) :
    ∀ ell, 0 ≤ ell → ell ≤ 1 → ∀ r i (a : packet.s r i) observer k, 1 ≤ k →
      let choice := round3PreparedParameterSecondaryChoice Data hd hs i r _ (packet.piece r i a)
      let native := (choice.pullback (Data.parameterChart observer.2)).toNative
      let t := ((OpenPartialHomeomorph.refl Ep).prod (Data.atlas.chart observer.1)).symm.trans native.chart
      ∀ z, parameterTensorModelEquiv (m+1) d z ∈ incrementsOriginalEvaluation Data.atlas Data.parameterChart
        Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet observer →
        ((Data.parameterChart observer.2).symm z.1,(Data.atlas.chart observer.1).symm z.2) ∈
          round3PreparedParameterSecondaryCarrier Data r choice →
        ell^(k-1)*‖iteratedFDeriv ℝ k t z‖ ≤ budget.forwardProfile k ∧
        ell^(k-1)*‖iteratedFDeriv ℝ k t.symm (t z)‖ ≤ budget.inverseProfile k := by
  intro ell hell hellOne r i a observer k hk choice native t z hz hCarrier
  let piece := packet.piece r i a
  have hPreserves : Round3ParameterChartPreserves piece.native :=
    (round3_prepared_signed_native_preserves_phase Data hd hs i r _ piece).1
  let b := round3ParameterCrossNativeChart (Data.parameterChart i.2)
    (Data.parameterChart observer.2) piece.native
  have hChart : native.chart = actualHostAdaptedChart (Data.atlas.chart i.1) b :=
    (round3Parameter_cross_host_conjugation (Data.parameterChart i.2)
      (Data.parameterChart observer.2) (Data.atlas.chart i.1) piece.native hPreserves).symm
  have hEval := (actual_original_native_evaluation_iff Data hd observer z).mp hz
  have hp : z.1 ∈ (Data.parameterChart observer.2).target := hd.parameter_norm_subset observer.2 hEval.2.1
  have hx : z.2 ∈ (Data.atlas.chart observer.1).target := hd.source_norm_subset observer.1 hEval.1
  have hSource : z ∈ t.source := by
    refine ⟨⟨mem_univ _,hx⟩,?_⟩
    apply (round3ParameterChartPullback_source_iff (Data.parameterChart observer.2) choice.chart
      (round3_prepared_parameter_secondary_preserves Data hd hs i r _ piece)
      (z.1,(Data.atlas.chart observer.1).symm z.2) hp).mpr
    exact packet.source r i a hCarrier
  have hNativeSource : ∀ y ∈ piece.native.source,
      y.1 ∈ Data.parameterNormDomain i.2 ∧ y.2 ∈ Data.sourceNormDomain i.1 := by
    intro y hy
    have h := (actual_original_native_evaluation_iff Data hd i y).mp (budget.samples r i a y hy)
    exact ⟨h.2.1,h.1⟩
  have hJets := repairEntrance_original_native_observer_jets Data hd i.2 i.1 piece.native
    _ piece.slices piece.data hPreserves budget.nativeForward budget.nativeInverse
    budget.parameterTransition budget.sourceTransition budget.nativeForward_nonneg budget.nativeInverse_nonneg
    budget.parameterTransition_nonneg budget.sourceTransition_nonneg budget.transition
    (budget.forward r i a) (budget.inverse r i a) hNativeSource budget.parameterValue budget.sourceValue
    observer z hEval.2.1 hEval.1
    (budget.parameter_value observer.2 z.1 hEval.2.1) (budget.source_value observer.1 z.2 hEval.1)
  have ht : t = ((OpenPartialHomeomorph.refl Ep).prod (Data.atlas.chart observer.1)).symm.trans
      (actualHostAdaptedChart (Data.atlas.chart i.1) b) := by
    dsimp only [t]
    rw [hChart]
  have hAt := hJets (ht ▸ hSource) k
  rw [← ht] at hAt
  refine ⟨?_,?_⟩
  · exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hell hellOne)).trans hAt.1
  · exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hell hellOne)).trans hAt.2

theorem original_secondary_numerical_cutoff_profiles
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (mu Mb buffer : ℝ) (hmu : 0 < mu) (hMb : 0 ≤ Mb) (hbuffer : 0 < buffer)
    (BS TS BP TP : ℕ → ℝ)
    (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (B : TensorBufferedChartFamily (Fin Ref.parameterCount) P Ep)
    (hChart : B.chart = Ref.parameterChart)
    (RS : TensorRawCutoffPreparation Ref.atlas BS TS Ds)
    (RP : TensorLocalRawPreparation B Ref.parameterSet BP TP Dp) :
    let theta := round3ParameterProductParent Ref.atlas B (squareNormalizedCutoff RS.raw)
      (tensorLocalNormalizedCutoff RP.raw)
    ∀ (packet : Round3PreparedParameterSecondaryPacket Ref hd hs theta)
      (hLiteral : ∀ r i a, (packet.piece r i a).cutoff = actualHostRefinementCutoff
        (actualOriginalHostJointChart («Ep» := Ep) (Ref.atlas.chart i.1))
        (round3ParameterNativeParent (Ref.parameterChart i.2) (theta i))
        (actualRefinementCutoff Z (packet.s r i) (buffer/actualPhaseRefinementFactor mu Mb) a.val))
      (hScalar : ∀ r i j (a : packet.s r i) x,
        buffer^j*‖iteratedFDeriv ℝ j
          (actualRefinementCutoff Z (packet.s r i) (buffer/actualPhaseRefinementFactor mu Mb) a.val) x‖ ≤
            (actualPhaseRefinementFactor mu Mb)^j*actualRefinementCutoffJetCost Z j),
    ∀ ell, 0 ≤ ell → ell ≤ 1 → ∀ r i (a : packet.s r i) observer n k, k ≤ n →
      let choice := round3PreparedParameterSecondaryChoice Ref hd hs i r _ (packet.piece r i a)
      ∀ z, parameterTensorModelEquiv (m+1) d z ∈ incrementsOriginalEvaluation Ref.atlas Ref.parameterChart
        Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet observer →
        ell^k*‖iteratedFDeriv ℝ k (fun y : Z => choice.cutoff
          ((Ref.parameterChart observer.2).symm y.1,(Ref.atlas.chart observer.1).symm y.2)) z‖ ≤
            incrementSecondaryCutoffProfile Z mu Mb buffer BS TS BP TP Ds Dp n := by
  intro theta packet hLiteral hScalar ell hell hell1 r i a observer n k hkn choice z hz
  let chi := parameterLocalProductCutoff Ref.atlas B (squareNormalizedCutoff RS.raw)
    (tensorLocalNormalizedCutoff RP.raw)
  have hB : ∀ p, B.chart p ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [hChart]
    exact hd.parameter_charts_smooth
  obtain ⟨O,hO,hKO,hChi,hPart,hSupport,hCount,hJets,hTransition⟩ :=
    round4_actual_product_smoothing_providers BS TS BP TP hBS hTS hBP hTP Ds Dp
      Ref.parameterCount Ref.atlas B hd.atlas_smooth hB Ref.parameterSet RS RP
  let q := (parameterLocalProductFamily Ref.atlas B).chart i
  let e := (parameterLocalProductFamily Ref.atlas B).chart observer
  let phi := actualRefinementCutoff Z (packet.s r i) (buffer/actualPhaseRefinementFactor mu Mb) a.val
  let Parent := round4ParentProfile BS TS BP TP Ds Dp
  let Scalar := incrementScalarCutoffProfile Z mu Mb buffer
  let Transition := fun j => max (TP j) (TS j)
  have hP : ∀ j, 0 ≤ Parent j := round4ParentProfile_nonneg hBS hTS hBP hTP Ds Dp
  have hSc : ∀ j, 0 ≤ Scalar j := incrementScalarCutoffProfile_nonneg Z mu Mb buffer hmu hMb hbuffer
  have hT : ∀ j, 0 ≤ Transition j := fun j => le_max_of_le_left (hTP j)
  have hThetaSupport : tsupport (theta i) ⊆ q.source :=
    (round3ParameterProductParent_tsupport Ref.atlas B _ _ i).trans
      ((hSupport i).trans ((parameterLocalProductFamily Ref.atlas B).inner_subset i))
  have hTheta : ContMDiff 𝓘(ℝ,Z) 𝓘(ℝ,ℝ) ∞ (theta i) := (hChi i).mul (hChi i)
  have hOldLiteral := increment_actual_secondary_cutoff_literal Ref hd hs i r _ (packet.piece r i a)
    (theta i) phi (by
      intro y hy
      have h := hThetaSupport hy
      change y.1 ∈ (B.chart i.2).source ∧ y.2 ∈ (Ref.atlas.chart i.1).source at h
      rwa [hChart] at h) (hLiteral r i a)
  have hPhysical : choice.cutoff = fun y => theta i y*phi (q y) := by
    rw [hOldLiteral]
    funext y
    change theta i y*phi (Ref.parameterChart i.2 y.1,Ref.atlas.chart i.1 y.2) =
      theta i y*phi (B.chart i.2 y.1,Ref.atlas.chart i.1 y.2)
    rw [hChart]
  have hEval := (actual_original_native_evaluation_iff Ref hd observer z).mp hz
  have hez : z ∈ e.target := by
    change z.1 ∈ (B.chart observer.2).target ∧ z.2 ∈ (Ref.atlas.chart observer.1).target
    rw [hChart]
    exact ⟨hd.parameter_norm_subset observer.2 hEval.2.1,hd.source_norm_subset observer.1 hEval.1⟩
  have hBound := increment_physical_refinement_observer_jets q e
    (parameterLocalProductFamily_chart_mem Ref.atlas B hd.atlas_smooth hB i)
    (parameterLocalProductFamily_chart_mem Ref.atlas B hd.atlas_smooth hB observer)
    (theta i) choice.cutoff phi hTheta (actualRefinementCutoff_contDiff Z _ _ _) hThetaSupport hPhysical
    Parent Scalar Transition hP hSc hT (by
      intro j y
      apply (le_div_iff₀ (pow_pos hbuffer j)).mpr
      simpa only [mul_comm] using hScalar r i j a y) z hez (by
      intro j
      simpa only [one_pow,one_mul] using round4_actual_product_parent_jets BS TS BP TP hBS hTS hBP hTP
        Ds Dp Ref.atlas B hd.atlas_smooth hB Ref.parameterSet RS RP observer i j 1 (by norm_num) le_rfl z hez) (by
      intro hActive j hj
      exact hTransition observer i j hj z hez
        (round3ParameterProductParent_tsupport Ref.atlas B _ _ i hActive)) k
  have hRho : (fun y : Z => choice.cutoff
      ((Ref.parameterChart observer.2).symm y.1,(Ref.atlas.chart observer.1).symm y.2)) = choice.cutoff ∘ e.symm := by
    funext y
    change choice.cutoff ((Ref.parameterChart observer.2).symm y.1,(Ref.atlas.chart observer.1).symm y.2) =
      choice.cutoff ((B.chart observer.2).symm y.1,(Ref.atlas.chart observer.1).symm y.2)
    rw [hChart]
  rw [hRho]
  exact ((mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hell hell1)).trans hBound).trans
    (originalSecondaryCutoffPrefix_bound _ (tensorProductJetConstant_nonneg hP
      (repairEntranceCompositionProfile_nonneg Scalar Transition hSc hT)) hkn)


def originalSecondaryCompletionProfiles
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (BS TS BP TP : ℕ → ℝ)
    (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (B : TensorBufferedChartFamily (Fin Data.parameterCount) P Ep)
    (hChart : B.chart=Data.parameterChart)
    (RS : TensorRawCutoffPreparation Data.atlas BS TS Ds)
    (RP : TensorLocalRawPreparation B Data.parameterSet BP TP Dp)
    (packet : Round3PreparedParameterSecondaryPacket Data hd hs
      (round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
        (tensorLocalNormalizedCutoff RP.raw)))
    (budget : IncrementSecondaryChartBudget Data hd hs _ packet) :
    IncrementsCompletionSecondaryPacketProfiles Data hd hs _ packet where
  Tinv := budget.inverseProfile
  Kcut := budget.cutoffProfile BS TS BP TP Ds Dp
  Tobs := budget.forwardProfile
  inverse_nonneg := budget.inverseProfile_nonneg
  cutoff_nonneg := budget.cutoffProfile_nonneg BS TS BP TP Ds Dp hBS hTS hBP hTP
  observer_nonneg := budget.forwardProfile_nonneg
  positive := original_secondary_numerical_positive_profiles Data hd hs _ packet budget
  cutoff := original_secondary_numerical_cutoff_profiles Data hd hs
    budget.mu budget.Mb budget.buffer budget.mu_pos budget.Mb_nonneg budget.buffer_pos
    BS TS BP TP hBS hTS hBP hTP Ds Dp B hChart RS RP packet budget.literal budget.scalar

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_secondary_numerical_positive_profiles
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_secondary_numerical_cutoff_profiles
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.originalSecondaryCompletionProfiles
