import Repair.IncrementLiteralCutoff
import Repair.IncrementCutoffObserverJets
import Repair.IncrementActualSecondaryPacket
import Probes.Round3PreparedParameterSecondaryStableProfiles
import Smoothing.Round4ParentFiniteProfiles

/-! The literal secondary cutoffs have one numerical host profile. It is
computed from the actual original raw source/parameter preparations and the
actual scalar refinement radius. No maximum of produced cutoff jets occurs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Filter IsManifold
open scoped ContDiff Topology Classical BigOperators
namespace GlobalEmbedding.Continuation

variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

def incrementScalarCutoffProfile (mu Mb buffer : ℝ) (j : ℕ) : ℝ :=
  (actualPhaseRefinementFactor mu Mb)^j*actualRefinementCutoffJetCost X j/buffer^j

theorem incrementScalarCutoffProfile_nonneg (mu Mb buffer : ℝ)
    (hmu : 0 < mu) (hMb : 0 ≤ Mb) (hbuffer : 0 < buffer) (j : ℕ) :
    0 ≤ incrementScalarCutoffProfile X mu Mb buffer j :=
  div_nonneg (mul_nonneg (pow_nonneg (actualPhaseRefinementFactor_pos hmu hMb).le j)
    (actualRefinementCutoffJetCost_nonneg X j)) (pow_nonneg hbuffer.le j)

def incrementSecondaryCutoffProfile (mu Mb buffer : ℝ) (BS TS BP TP : ℕ → ℝ) (Ds Dp n : ℕ) : ℝ :=
  bufferedTransitionPrefix (tensorProductJetConstant (round4ParentProfile BS TS BP TP Ds Dp)
    (repairEntranceCompositionProfile (incrementScalarCutoffProfile X mu Mb buffer)
      (fun j => max (TP j) (TS j)))) n

theorem incrementSecondaryCutoffProfile_nonneg (mu Mb buffer : ℝ) (BS TS BP TP : ℕ → ℝ) (Ds Dp n : ℕ)
    (hmu : 0 < mu) (hMb : 0 ≤ Mb) (hbuffer : 0 < buffer)
    (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j) :
    0 ≤ incrementSecondaryCutoffProfile X mu Mb buffer BS TS BP TP Ds Dp n :=
  zero_le_one.trans (one_le_bufferedTransitionPrefix
    (tensorProductJetConstant_nonneg (round4ParentProfile_nonneg hBS hTS hBP hTP Ds Dp)
      (repairEntranceCompositionProfile_nonneg _ _
        (incrementScalarCutoffProfile_nonneg X mu Mb buffer hmu hMb hbuffer)
        (fun j => le_max_of_le_left (hTP j)))) n)

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

private theorem secondaryCutoffPrefix_bound (P : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j)
    {k j : ℕ} (hkj : k ≤ j) : P k ≤ bufferedTransitionPrefix P j := by
  have h := Finset.single_le_sum (fun l (_ : l ∈ Finset.range (j+1)) => hP l)
    (show k ∈ Finset.range (j+1) by simp; omega)
  exact h.trans (by unfold bufferedTransitionPrefix; linarith)

theorem increment_actual_secondary_host_cutoff_profiles
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
    ∀ (F : P → M → Ey) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p))
      (stable : ∀ r i (a : packet.s r i), Round3PreparedParameterStableSecondaryPiece Ref hd hs i r _ (packet.piece r i a) F hF)
      ell, 0 ≤ ell → ell ≤ 1 → ∀ r i (a : packet.s r i) observer n k, k ≤ n →
      let choice := round3PreparedParameterSecondaryChoice Ref hd hs i r _ (stable r i a).piece
      ∀ z, parameterTensorModelEquiv (m+1) d z ∈ incrementsOriginalEvaluation Ref.atlas Ref.parameterChart
        Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet observer →
        ell^k*‖iteratedFDeriv ℝ k (fun y : Z => choice.cutoff
          ((Ref.parameterChart observer.2).symm y.1,(Ref.atlas.chart observer.1).symm y.2)) z‖ ≤
            incrementSecondaryCutoffProfile Z mu Mb buffer BS TS BP TP Ds Dp n := by
  intro theta packet hLiteral hScalar F hF stable ell hell hell1 r i a observer n k hkn choice z hz
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
  have hEqual := (round3_prepared_parameter_secondary_stable_functions Ref hd hs i r _
    (packet.piece r i a) F hF (stable r i a) observer.2).1
  have hPhysical : choice.cutoff = fun y => theta i y*phi (q y) := by
    rw [hEqual,hOldLiteral]
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
    (secondaryCutoffPrefix_bound _ (tensorProductJetConstant_nonneg hP
      (repairEntranceCompositionProfile_nonneg Scalar Transition hSc hT)) hkn)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.increment_actual_secondary_host_cutoff_profiles
