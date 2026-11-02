import Smoothing.Round3OuterHostObserverProfile
import Smoothing.Round3OuterHostReferenceProfile

/-! All three derivative inputs of the actual normal-cover consumer are
produced from fixed reference charts and the original fixed packet. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology ENNReal BigOperators
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
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

def round3HostObserverProfile (m d : ℕ) (Forward Given : ℕ → ℝ) (j : ℕ) : ℝ :=
  (actualFastChartTransferCost
    (fun _ => actualOriginalNativeGivenTransitionJetCost (m+1) d j*Given j) j *
      (∑ k ∈ Finset.range (j+2), Forward k)) *
        linearModelFactor (parameterTensorModelEquiv (m+1) d).symm j

def round3HostReferenceProfile (m d N : ℕ) (T Given : ℕ → ℝ) (j : ℕ) : ℝ :=
  actualFastChartTransferPrefix T j*(actualOriginalNormalJetCost (m+1) d N j*Given j)

theorem round3HostObserverProfile_nonneg (m d : ℕ) (Forward Given : ℕ → ℝ)
    (hForward : ∀ j, 0 ≤ Forward j) (hGiven : ∀ j, 0 ≤ Given j) (j : ℕ) :
    0 ≤ round3HostObserverProfile m d Forward Given j :=
  mul_nonneg (mul_nonneg (actualFastChartTransferCost_nonneg _
    (fun _ => mul_nonneg (actualOriginalNativeGivenTransitionJetCost_nonneg _ _ _) (hGiven j)) j)
      (Finset.sum_nonneg (fun k _ => hForward k))) (linearModelFactor_nonneg _ _)

theorem round3HostReferenceProfile_nonneg (m d N : ℕ) (T Given : ℕ → ℝ)
    (hT : ∀ j, 0 ≤ T j) (hGiven : ∀ j, 0 ≤ Given j) (j : ℕ) :
    0 ≤ round3HostReferenceProfile m d N T Given j :=
  mul_nonneg (actualFastChartTransferPrefix_nonneg T hT j)
    (mul_nonneg (actualOriginalNormalJetCost_nonneg _ _ _ _) (hGiven j))

theorem round3_actual_host_normal_cover_fixed_profiles
    {A : Type*}
    (Data : IncrementsOriginalNativeData (m+1) d N M Ep)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hId : ∀ ip, Data.parameterChart ip = OpenPartialHomeomorph.refl Ep)
    (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (fun x => Data.F (p,x)))
    (nu : Fin Data.primaryCount) (domain : Set (Ep × M))
    (host : A → Fin Data.atlas.count) (b : A → OpenPartialHomeomorph X X)
    (e : A → Ep → OpenPartialHomeomorph M D)
    (hData : ∀ a, ActualOriginalHostSliceData (Data.atlas.chart (host a)) (b a) (Data.phase nu) (e a))
    (hActive : ∀ a, (actualHostAdaptedChart (Data.atlas.chart (host a)) (b a)).source ⊆
      Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data)
    (hInner : ∀ a w, w ∈ (actualHostAdaptedChart (Data.atlas.chart (host a)) (b a)).source →
      w.2 ∈ Data.atlas.inner (host a))
    (hCover : ∀ w ∈ domain, ∃ a, w ∈ (actualHostAdaptedChart (Data.atlas.chart (host a)) (b a)).source)
    (cF cT mu : ℝ)
    (hFirst : ∀ a z, z ∈ (b a).target → ∀ w : D, cF*‖w‖^2 ≤
      ‖fderiv ℝ ((fun x => Data.F (z.1,x)) ∘ (e a z.1).symm) z.2 w‖^2)
    (hFrame : ∀ a z, z ∈ (b a).target → ∀ w : Tdata, cT*‖w‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame (fun x => Data.F (z.1,x)) (hF z.1)
        (e a z.1).symm z.2 w‖^2)
    (hReserve : ∀ a z, z ∈ (b a).target → mu ≤
      ‖actualOriginalFreeNormalFieldRaw (fun p x => Data.F (p,x)) hF (e a)
        (fun z : X => Data.freeNormal nu (z.1,(e a z.1).symm z.2)) z‖)
    (T Forward Given : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j) (hForward : ∀ j, 0 ≤ Forward j)
    (hFixed : ∀ j, parameterRound2_originalFixedPacketProfile Data j 1 ≠ ⊤)
    (hGiven : ∀ j, (parameterRound2_originalFixedPacketProfile Data j 1).toReal ≤ Given j)
    (hInv : ∀ a k z, z ∈ (b a).target → ‖iteratedFDeriv ℝ k (b a).symm z‖ ≤ T k)
    (hForw : ∀ a k z, z ∈ (b a).source → ‖iteratedFDeriv ℝ k (b a) z‖ ≤ Forward k) :
    let cover := round3HostNormalCover Data hd hs hId hF nu domain host b e
      hData hActive hInner hCover cF cT mu hFirst hFrame hReserve
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
  have hGeometry (a : A) := actual_host_slice_geometry_inputs
    (Data.atlas.chart (host a)) (hd.atlas_smooth.chart_mem (host a)) (b a) (Data.phase nu) (e a) (hData a)
  refine ⟨?_,?_,?_⟩
  · intro i a k hk y hy
    have hz : cover.forward i a y ∈ (b a).target := cover.forward_maps i a hy.2
    rcases hData a with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hadapt,hback,hforward,hbj,hfj⟩
    change ‖iteratedFDeriv ℝ k (actualSourceChartTransition (fun _ => Data.atlas.chart (host a))
      (e a)) (cover.forward i a y)‖ ≤ T k
    rw [hbj k _ hz]
    exact hInv a k _ hz
  · intro i a k hk y hy
    have hB : 0 ≤ ∑ l ∈ Finset.range (k+2), Forward l :=
      Finset.sum_nonneg (fun l _ => hForward l)
    have hh := round3_actual_host_observer_fixed_profile Data hd hId i (host a) (b a)
      (hGeometry a).2.1 k (Given k) (∑ l ∈ Finset.range (k+2), Forward l) hB
      (hFixed k) (hGiven k)
      (by
        intro l hl hlk z hz
        exact (hForw a l z hz).trans (Finset.single_le_sum
          (fun t _ => hForward t) (by simp; omega)))
      k hk (by omega) y ⟨hy.1.1,hy.2⟩
    exact hh
  · intro i a k y hy
    exact round3_actual_host_reference_fixed_profile Data hd hs hId (host a,i.2) nu (b a) (e a)
      (hData a) (hActive a) T hT k (Given k) (hFixed k) (hGiven k)
      (fun l _ _ z hz => hInv a l z hz) _ (cover.forward_maps i a hy.2) (cover.sample i a y hy)

#print axioms round3_actual_host_normal_cover_fixed_profiles
end GlobalEmbedding.Continuation
