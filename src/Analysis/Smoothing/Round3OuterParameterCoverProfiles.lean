import Smoothing.Round3OuterParameterObserverProfile
import Smoothing.Round3OuterParameterReferenceProfile
import Smoothing.Round3OuterHostCoverProfiles

/-! Actual generic-parameter normal profiles use only fixed-reference
chart derivatives at the genuine original samples. Cross-parameter chart
bounds are never extended to unsampled chart boundaries. All three inputs
of the actual normal-stage consumer are proved for the same cover. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Y" => Fin (m+1+d) → ℝ
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
private local instance hostCoverFirstNormed : NormedAddCommGroup (D →L[ℝ] Ey) := inferInstance
private local instance hostCoverFirstSpace : NormedSpace ℝ (D →L[ℝ] Ey) := inferInstance
private local instance hostCoverFrameNormed : NormedAddCommGroup (Tdata →L[ℝ] Ey) := inferInstance
private local instance hostCoverFrameSpace : NormedSpace ℝ (Tdata →L[ℝ] Ey) := inferInstance

theorem round3_parameter_host_normal_cover_fixed_profiles
    {A : Type*}
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (fun x => Data.F (p,x)))
    (nu : Fin Data.primaryCount) (domain : Set (P × M))
    (host : Fin Data.parameterCount → A → Fin Data.atlas.count)
    (b : Fin Data.parameterCount → A → OpenPartialHomeomorph X X)
    (e : Fin Data.parameterCount → A → Ep → OpenPartialHomeomorph M D)
    (hData : ∀ ip a, ActualOriginalHostSliceData (Data.atlas.chart (host ip a)) (b ip a)
      (fun w : Ep × M => Data.phase nu ((Data.parameterChart ip).symm w.1,w.2)) (e ip a))
    (hNative : ∀ ip a, (b ip a).source ⊆ actualOriginalNativeOpen Data (host ip a,ip))
    (hActive : ∀ ip a w, w ∈ (actualHostAdaptedChart (Data.atlas.chart (host ip a)) (b ip a)).source →
      ((Data.parameterChart ip).symm w.1,w.2) ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data)
    (hInner : ∀ ip a w, w ∈ (actualHostAdaptedChart (Data.atlas.chart (host ip a)) (b ip a)).source →
      w.2 ∈ Data.atlas.inner (host ip a))
    (carrier : Fin Data.parameterCount → A → Set (Ep × M))
    (hCarrierOpen : ∀ ip a, IsOpen (carrier ip a))
    (hCarrierSub : ∀ ip a, carrier ip a ⊆ (actualHostAdaptedChart (Data.atlas.chart (host ip a)) (b ip a)).source)
    (hCover : ∀ ip (w : Ep × M), w.1 ∈ (Data.parameterChart ip).target →
      ((Data.parameterChart ip).symm w.1,w.2) ∈ domain →
      ∃ a, w ∈ carrier ip a)
    (cF cT mu : ℝ)
    (hFirst : ∀ ip a z, z ∈ (b ip a).target → ∀ w : D, cF*‖w‖^2 ≤
      ‖fderiv ℝ ((fun x => Data.F ((Data.parameterChart ip).symm z.1,x)) ∘ (e ip a z.1).symm) z.2 w‖^2)
    (hFrame : ∀ ip a z, z ∈ (b ip a).target → ∀ w : Tdata, cT*‖w‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame (fun x => Data.F ((Data.parameterChart ip).symm z.1,x))
        (hF ((Data.parameterChart ip).symm z.1)) (e ip a z.1).symm z.2 w‖^2)
    (hReserve : ∀ ip a z, z ∈ (b ip a).target → mu ≤
      ‖actualOriginalFreeNormalFieldRaw (fun p x => Data.F ((Data.parameterChart ip).symm p,x))
        (fun p => hF ((Data.parameterChart ip).symm p)) (e ip a)
        (fun z : X => Data.freeNormal nu ((Data.parameterChart ip).symm z.1,(e ip a z.1).symm z.2)) z‖)
    (T Forward Given : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j) (hForward : ∀ j, 0 ≤ Forward j)
    (hFixed : ∀ j, parameterRound2_originalFixedPacketProfile Data j 1 ≠ ⊤)
    (hGiven : ∀ j, (parameterRound2_originalFixedPacketProfile Data j 1).toReal ≤ Given j)
    (hInv : ∀ ip a k z, z ∈ (b ip a).target ∩
      (actualHostAdaptedChart (Data.atlas.chart (host ip a)) (b ip a)).symm ⁻¹' carrier ip a →
      parameterTensorModelEquiv (m+1) d ((b ip a).symm z) ∈
        incrementsOriginalEvaluation Data.atlas Data.parameterChart
          Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet (host ip a,ip) →
      ‖iteratedFDeriv ℝ k (b ip a).symm z‖ ≤ T k)
    (hForw : ∀ (i : Fin Data.atlas.count × Fin Data.parameterCount) a k y,
      y ∈ incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet i ∩
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart i ∩
        (round3OriginalNativeObserverPoint Data i) ⁻¹' carrier i.2 a) →
      ‖iteratedFDeriv ℝ k (b i.2 a)
        ((actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart (host i.2 a)))
          (round3OriginalNativeObserverPoint Data i y))‖ ≤ Forward k) :
    let cover := round3ParameterHostNormalCover Data hd hs hF nu domain host b e
      hData hNative hActive hInner carrier hCarrierOpen hCarrierSub hCover cF cT mu hFirst hFrame hReserve
    let Samples := fun i => incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i ∩
      (incrementsOriginalJointPoint Data.atlas Data.parameterChart i) ⁻¹' domain
    (∀ i a k, 1 ≤ k → ∀ y ∈ Samples i ∩ cover.original i a,
      ‖iteratedFDeriv ℝ k (round3OriginalAdaptedTransition Data.atlas
        (cover.host i a).1 (cover.chart i a)) (cover.forward i a y)‖ ≤ T k) ∧
    (∀ i a k, 1 ≤ k → ∀ y ∈ Samples i ∩ cover.original i a,
      ‖iteratedFDeriv ℝ k (cover.forward i a) y‖ ≤ round3HostObserverProfile m d Forward Given k) ∧
    (∀ i a k, ∀ y ∈ Samples i ∩ cover.original i a,
      ‖iteratedFDeriv ℝ k (round3NormalChartReference Data (cover.host i a)
        (cover.chart i a) (Data.freeNormal nu)) (cover.forward i a y)‖ ≤
          round3HostReferenceProfile m d N T Given k) := by
  intro cover Samples
  have hGeometry (ip) (a : A) := actual_host_slice_geometry_inputs
    (Data.atlas.chart (host ip a)) (hd.atlas_smooth.chart_mem (host ip a)) (b ip a) _ (e ip a) (hData ip a)
  refine ⟨?_,?_,?_⟩
  · intro i a k hk y hy
    have hzNative := cover.forward_maps i a hy.2
    have hz : cover.forward i a y ∈ (b i.2 a).target := hzNative.1
    have hSample := cover.sample i a y hy
    rcases hData i.2 a with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hadapt,hback,hforward,hbj,hfj⟩
    change parameterTensorModelEquiv (m+1) d
      (actualSourceChartTransition (fun _ => Data.atlas.chart (host i.2 a)) (e i.2 a)
        (cover.forward i a y)) ∈ _ at hSample
    rw [hback hz] at hSample
    change ‖iteratedFDeriv ℝ k (actualSourceChartTransition (fun _ => Data.atlas.chart (host i.2 a))
      (e i.2 a)) (cover.forward i a y)‖ ≤ T k
    rw [hbj k _ hz]
    exact hInv i.2 a k _ hzNative hSample
  · intro i a k hk y hy
    have hB : 0 ≤ ∑ l ∈ Finset.range (k+2), Forward l :=
      Finset.sum_nonneg (fun l _ => hForward l)
    have hh := round3_parameter_host_observer_fixed_profile Data hd i (host i.2 a) (b i.2 a)
      (hGeometry i.2 a).2.1 (carrier i.2 a) (hCarrierOpen i.2 a) (hCarrierSub i.2 a)
      k (Given k) (∑ l ∈ Finset.range (k+2), Forward l) hB
      (hFixed k) (hGiven k)
      (by
        intro l hl hlk z hz
        exact (hForw i a l z hz).trans (Finset.single_le_sum
          (fun t _ => hForward t) (by simp; omega)))
      k hk (by omega) y ⟨hy.1.1,hy.2⟩
    exact hh
  · intro i a k y hy
    exact round3_parameter_host_reference_fixed_profile Data hd hs (host i.2 a,i.2) nu
      (b i.2 a) (e i.2 a) (hData i.2 a) (hNative i.2 a) (fun w hw => (hActive i.2 a w hw).1)
      T hT k (Given k) (hFixed k) (hGiven k)
      ((b i.2 a).target ∩ (actualHostAdaptedChart (Data.atlas.chart (host i.2 a)) (b i.2 a)).symm ⁻¹' carrier i.2 a)
      inter_subset_left
      (fun l _ _ z hz hS => hInv i.2 a l z hz hS) _ (cover.forward_maps i a hy.2) (cover.sample i a y hy)

#print axioms round3_parameter_host_normal_cover_fixed_profiles
end GlobalEmbedding.Continuation
