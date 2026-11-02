import OriginalIncrements.SourceSampleSecondaryProfiles
import Repair.SourceCollarNovParameterGerm

/-!
# The actual localized secondary cutoff has the original numerical profile

At every observed original parameter, the localization is one on an open
neighborhood. The actual cutoff therefore has exactly the same mixed jets
as the unlocalized raw parent times the same scalar grid cutoff. No
parameter-localization derivative budget enters the common profile, and
no open construction domain is required to lie inside K.
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

private theorem localizedSecondaryCutoffPrefix_bound (P : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j)
    {k j : ℕ} (hkj : k ≤ j) : P k ≤ bufferedTransitionPrefix P j := by
  have h := Finset.single_le_sum (fun l (_ : l ∈ Finset.range (j+1)) => hP l)
    (show k ∈ Finset.range (j+1) by simp; omega)
  exact h.trans (by unfold bufferedTransitionPrefix; linarith)

theorem localized_source_sample_secondary_cutoff_profiles
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (mu Mb buffer : ℝ) (hmu : 0 < mu) (hMb : 0 ≤ Mb) (hbuffer : 0 < buffer)
    (BS TS BP TP : ℕ → ℝ)
    (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (B : TensorBufferedChartFamily (Fin Ref.parameterCount) P Ep)
    (hChart : B.chart = Ref.parameterChart)
    (RS : TensorRawCutoffPreparation Ref.atlas BS TS Ds)
    (RP : TensorLocalRawPreparation B Ref.parameterSet BP TP Dp)
    (psi : P → ℝ) (V : Set P) (hV : IsOpen V)
    (hKV : Ref.parameterSet ⊆ V) (hOne : EqOn psi 1 V) :
    let theta0 := round3ParameterProductParent Ref.atlas B (squareNormalizedCutoff RS.raw)
      (tensorLocalNormalizedCutoff RP.raw)
    let theta := fun i => sourceCollarNovParameterLocalized psi (theta0 i)
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
  intro theta0 theta packet hLiteral hScalar ell hell hell1 r i a observer n k hkn choice z hz
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
  have hThetaSupport : tsupport (theta0 i) ⊆ q.source :=
    (round3ParameterProductParent_tsupport Ref.atlas B _ _ i).trans
      ((hSupport i).trans ((parameterLocalProductFamily Ref.atlas B).inner_subset i))
  have hTheta : ContMDiff 𝓘(ℝ,Z) 𝓘(ℝ,ℝ) ∞ (theta0 i) := (hChi i).mul (hChi i)
  have hLocalizedSource : tsupport (theta i) ⊆ q.source :=
    (sourceCollarNov_parameter_localized_tsupport psi (theta0 i)).trans
      (inter_subset_left.trans hThetaSupport)
  have hOldLiteral := increment_actual_secondary_cutoff_literal Ref hd hs i r _ (packet.piece r i a)
    (theta i) phi (by
      intro y hy
      have h := hLocalizedSource hy
      change y.1 ∈ (B.chart i.2).source ∧ y.2 ∈ (Ref.atlas.chart i.1).source at h
      rwa [hChart] at h) (hLiteral r i a)
  let base : P × M → ℝ := fun y => theta0 i y*phi (q y)
  have hPhysical : choice.cutoff = sourceCollarNovParameterLocalized psi base := by
    rw [hOldLiteral]
    funext y
    change (psi y.1*theta0 i y)*phi (Ref.parameterChart i.2 y.1,Ref.atlas.chart i.1 y.2) =
      psi y.1*(theta0 i y*phi (B.chart i.2 y.1,Ref.atlas.chart i.1 y.2))
    rw [hChart]
    ring
  have hEval := (actual_original_native_evaluation_iff Ref hd observer z).mp hz
  have hez : z ∈ e.target := by
    change z.1 ∈ (B.chart observer.2).target ∧ z.2 ∈ (Ref.atlas.chart observer.1).target
    rw [hChart]
    exact ⟨hd.parameter_norm_subset observer.2 hEval.2.1,hd.source_norm_subset observer.1 hEval.1⟩
  have hBound := increment_physical_refinement_observer_jets q e
    (parameterLocalProductFamily_chart_mem Ref.atlas B hd.atlas_smooth hB i)
    (parameterLocalProductFamily_chart_mem Ref.atlas B hd.atlas_smooth hB observer)
    (theta0 i) base phi hTheta (actualRefinementCutoff_contDiff Z _ _ _) hThetaSupport rfl
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
  have heK : (e.symm z).1 ∈ Ref.parameterSet := by
    change (B.chart observer.2).symm z.1 ∈ Ref.parameterSet
    rw [hChart]
    exact hEval.2.2
  have hGermJets := sourceCollarNov_parameter_localized_mixed_jets psi V Ref.parameterSet
    hV hKV hOne base e.symm z (e.symm.continuousAt hez) heK k
  rw [hRho,hPhysical,hGermJets]
  exact ((mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hell hell1)).trans hBound).trans
    (localizedSecondaryCutoffPrefix_bound _ (tensorProductJetConstant_nonneg hP
      (repairEntranceCompositionProfile_nonneg Scalar Transition hSc hT)) hkn)

/-- The same actual localized packet supplies all three completion
profiles at the numerical values, without compact maxima or K=univ. -/
def localizedSourceSampleSecondaryCompletionProfiles
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (BS TS BP TP : ℕ → ℝ)
    (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (B : TensorBufferedChartFamily (Fin Data.parameterCount) P Ep)
    (hChart : B.chart=Data.parameterChart)
    (RS : TensorRawCutoffPreparation Data.atlas BS TS Ds)
    (RP : TensorLocalRawPreparation B Data.parameterSet BP TP Dp)
    (psi : P → ℝ) (V : Set P) (hV : IsOpen V)
    (hKV : Data.parameterSet ⊆ V) (hOne : EqOn psi 1 V) :
    let theta := fun i => sourceCollarNovParameterLocalized psi
      (round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
        (tensorLocalNormalizedCutoff RP.raw) i)
    ∀ (packet : Round3PreparedParameterSecondaryPacket Data hd hs theta)
      (budget : SourceSampleSecondaryChartBudget Data hd hs theta packet),
      IncrementsCompletionSecondaryPacketProfiles Data hd hs theta packet := by
  intro theta packet budget
  exact {
    Tinv := budget.inverseProfile
    Kcut := budget.cutoffProfile BS TS BP TP Ds Dp
    Tobs := budget.forwardProfile
    inverse_nonneg := budget.inverseProfile_nonneg
    cutoff_nonneg := budget.cutoffProfile_nonneg BS TS BP TP Ds Dp hBS hTS hBP hTP
    observer_nonneg := budget.forwardProfile_nonneg
    positive := source_sample_secondary_positive_profiles Data hd hs theta packet budget
    cutoff := localized_source_sample_secondary_cutoff_profiles Data hd hs
      budget.mu budget.Mb budget.buffer budget.mu_pos budget.Mb_nonneg budget.buffer_pos
      BS TS BP TP hBS hTS hBP hTP Ds Dp B hChart RS RP psi V hV hKV hOne
      packet budget.literal budget.scalar }

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.localized_source_sample_secondary_cutoff_profiles
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.localizedSourceSampleSecondaryCompletionProfiles
