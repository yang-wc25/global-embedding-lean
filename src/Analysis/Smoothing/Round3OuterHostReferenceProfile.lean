import Smoothing.Round3OuterFixedHostNormal
import Smoothing.Round3OuterHostNormalCover

/-! Fixed reference normal profile on the same actual host target. The
genuine active source provides the original open domain; a literal original
sample supplies the quantitative bound. No current-map norm enters. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal Topology
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D

theorem round3_actual_host_reference_fixed_profile
    (Data : IncrementsOriginalNativeData (m+1) d N M Ep)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hId : ∀ ip, Data.parameterChart ip = OpenPartialHomeomorph.refl Ep)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (nu : Fin Data.primaryCount)
    (b : OpenPartialHomeomorph X X) (e : Ep → OpenPartialHomeomorph M D)
    (hdata : ActualOriginalHostSliceData (Data.atlas.chart i.1) b (Data.phase nu) e)
    (hActive : (actualHostAdaptedChart (Data.atlas.chart i.1) b).source ⊆
      Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (j : ℕ) (budget : ℝ)
    (hfinite : parameterRound2_originalFixedPacketProfile Data j 1 ≠ ⊤)
    (hbudget : (parameterRound2_originalFixedPacketProfile Data j 1).toReal ≤ budget)
    (hInv : ∀ k, 1 ≤ k → k ≤ j → ∀ z ∈ b.target,
      ‖iteratedFDeriv ℝ k b.symm z‖ ≤ T k)
    (z : X) (hz : z ∈ b.target)
    (hSample : parameterTensorModelEquiv (m+1) d
      (actualSourceChartTransition (fun _ => Data.atlas.chart i.1) e z) ∈
      incrementsOriginalEvaluation Data.atlas Data.parameterChart
        Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i) :
    ‖iteratedFDeriv ℝ j (fun w : X => Data.freeNormal nu
      ((Data.parameterChart i.2).symm w.1,(e w.1).symm w.2)) z‖ ≤
      actualFastChartTransferPrefix T j*(actualOriginalNormalJetCost (m+1) d N j*budget) := by
  have hdata' : ActualOriginalHostSliceData (Data.atlas.chart i.1) b
      (fun w : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm w.1,w.2)) e := by
    simpa only [hId,OpenPartialHomeomorph.refl_symm,OpenPartialHomeomorph.refl_apply,id_eq,
      Prod.mk.eta] using hdata
  have hg := actual_host_slice_geometry_inputs _ (hd.atlas_smooth.chart_mem i.1) _ _ _ hdata
  have hsource : b.source ⊆ actualOriginalNativeOpen Data i := by
    intro w hw
    have hc := (hg.1 hw).2
    have ha : (w.1,(Data.atlas.chart i.1).symm w.2) ∈
        (actualHostAdaptedChart (Data.atlas.chart i.1) b).source := by
      refine ⟨⟨mem_univ _,(Data.atlas.chart i.1).map_target hc⟩,?_⟩
      change (w.1,Data.atlas.chart i.1 ((Data.atlas.chart i.1).symm w.2)) ∈ b.source
      rwa [(Data.atlas.chart i.1).right_inv hc]
    have hphys := hActive ha
    have hcpt : (incrementsOriginalParameterPoint (parameterTensorModelEquiv (m+1) d w),
        incrementsOriginalSourcePoint (parameterTensorModelEquiv (m+1) d w)) = w :=
      (parameterTensorModelEquiv (m+1) d).symm_apply_apply w
    have hp := congrArg Prod.fst hcpt
    have hx := congrArg Prod.snd hcpt
    dsimp only at hp hx
    refine ⟨?_,?_⟩
    · change incrementsOriginalSourcePoint _ ∈ (Data.atlas.chart i.1).target ∧
        incrementsOriginalParameterPoint _ ∈ (Data.parameterChart i.2).target
      rw [hp,hx,hId]
      exact ⟨hc,mem_univ _⟩
    · change incrementsOriginalJointPoint Data.atlas Data.parameterChart i
        (parameterTensorModelEquiv (m+1) d w) ∈ incrementsOriginalParameterRegion Data
      rw [actual_original_jointPoint_native]
      simpa only [hId,OpenPartialHomeomorph.refl_symm,OpenPartialHomeomorph.refl_apply,id_eq] using hphys.2
  let S : Set X := b.target ∩ b.symm ⁻¹' ((parameterTensorModelEquiv (m+1) d) ⁻¹'
    incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i)
  have hzS : z ∈ S := by
    refine ⟨hz,?_⟩
    rcases hdata with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hadapt,hback,hforward,hbj,hfj⟩
    rwa [hback hz] at hSample
  have hnormal := round3_original_fixed_constructed_host_normal T hT j Data hd hs i nu b e hdata'
    S inter_subset_left hsource (fun _ hw => hw.2)
    (by
      intro w hw
      simpa only [hId,OpenPartialHomeomorph.refl_symm,OpenPartialHomeomorph.refl_apply,id_eq,
        Prod.mk.eta] using (hActive hw).1)
    1 budget (by norm_num) hfinite hbudget
    (by intro k hk hkj w hw; simpa only [one_pow,one_mul] using hInv k hk hkj w hw.1)
  simpa only [one_pow,one_mul] using hnormal.2 j le_rfl z hzS

#print axioms round3_actual_host_reference_fixed_profile
end GlobalEmbedding.Continuation
