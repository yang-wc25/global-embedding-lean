import Smoothing.Round3OuterFixedHostNormal
import Smoothing.Round3OuterParameterNormalCover

/-! Fixed reference normal profile on the same actual host target. The
genuine active source provides the original open domain; a literal original
sample supplies the quantitative bound. No current-map norm enters. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal Topology
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D

theorem round3_parameter_host_reference_fixed_profile
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (nu : Fin Data.primaryCount)
    (b : OpenPartialHomeomorph X X) (e : Ep → OpenPartialHomeomorph M D)
    (hdata : ActualOriginalHostSliceData (Data.atlas.chart i.1) b
      (fun w : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm w.1,w.2)) e)
    (hsource : b.source ⊆ actualOriginalNativeOpen Data i)
    (hActive : ∀ w ∈ (actualHostAdaptedChart (Data.atlas.chart i.1) b).source,
      ((Data.parameterChart i.2).symm w.1,w.2) ∈ Data.primaryDomain nu)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (j : ℕ) (budget : ℝ)
    (hfinite : parameterRound2_originalFixedPacketProfile Data j 1 ≠ ⊤)
    (hbudget : (parameterRound2_originalFixedPacketProfile Data j 1).toReal ≤ budget)
    (O : Set X) (hO : O ⊆ b.target)
    (hInv : ∀ k, 1 ≤ k → k ≤ j → ∀ z ∈ O,
      parameterTensorModelEquiv (m+1) d (b.symm z) ∈
        incrementsOriginalEvaluation Data.atlas Data.parameterChart
          Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i →
      ‖iteratedFDeriv ℝ k b.symm z‖ ≤ T k)
    (z : X) (hz : z ∈ O)
    (hSample : parameterTensorModelEquiv (m+1) d
      (actualSourceChartTransition (fun _ => Data.atlas.chart i.1) e z) ∈
      incrementsOriginalEvaluation Data.atlas Data.parameterChart
        Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i) :
    ‖iteratedFDeriv ℝ j (fun w : X => Data.freeNormal nu
      ((Data.parameterChart i.2).symm w.1,(e w.1).symm w.2)) z‖ ≤
      actualFastChartTransferPrefix T j*(actualOriginalNormalJetCost (m+1) d N j*budget) := by
  let S : Set X := O ∩ b.symm ⁻¹' ((parameterTensorModelEquiv (m+1) d) ⁻¹'
    incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i)
  have hzS : z ∈ S := by
    refine ⟨hz,?_⟩
    rcases hdata with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hadapt,hback,hforward,hbj,hfj⟩
    rwa [hback (hO hz)] at hSample
  have hnormal := round3_original_fixed_constructed_host_normal T hT j Data hd hs i nu b e hdata
    S (fun _ hw => hO hw.1) hsource (fun _ hw => hw.2)
    hActive
    1 budget (by norm_num) hfinite hbudget
    (by intro k hk hkj w hw; simpa only [one_pow,one_mul] using hInv k hk hkj w hw.1 hw.2)
  simpa only [one_pow,one_mul] using hnormal.2 j le_rfl z hzS

#print axioms round3_parameter_host_reference_fixed_profile
end GlobalEmbedding.Continuation
