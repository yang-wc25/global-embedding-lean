import Smoothing.Round3OuterFixedNormalJets
import Probes.ActualIncrementOriginalHostFields

/-! The reference normal on actual host-adapted charts, with all joint
jets derived from its original fixed packet and the reference inverse. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff ENNReal Topology
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × Es

theorem round3_host_original_field_jets
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (j : ℕ)
    (Data : IncrementsOriginalNativeData (m+1) d N M P) (hd : IncrementsOriginalDomainConditions Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (nu : Fin Data.primaryCount)
    (b : OpenPartialHomeomorph X X) (e : Ep → OpenPartialHomeomorph M Es)
    (hdata : ActualOriginalHostSliceData (Data.atlas.chart i.1) b
      (fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) e)
    (S : Set X) (hS : S ⊆ b.target)
    (hsource : b.source ⊆ actualOriginalPrimaryNativeOpen Data nu i)
    (hsample : MapsTo b.symm S
      ((parameterTensorModelEquiv (m+1) d) ⁻¹' incrementsOriginalPrimaryEvaluation Data nu i))
    (f : P × M → Y) (ell K : ℝ) (hell : 0 < ell) (hK : 0 ≤ K)
    (hf : ContDiffOn ℝ ∞ (fun z : X => f ((Data.parameterChart i.2).symm z.1,
      (Data.atlas.chart i.1).symm z.2)) (actualOriginalPrimaryNativeOpen Data nu i))
    (hfjet : ∀ k ≤ j, ∀ z, parameterTensorModelEquiv (m+1) d z ∈
      incrementsOriginalPrimaryEvaluation Data nu i → ell^k*‖iteratedFDeriv ℝ k
        (fun w : X => f ((Data.parameterChart i.2).symm w.1,(Data.atlas.chart i.1).symm w.2)) z‖ ≤ K)
    (hinvjet : ∀ k, 1 ≤ k → k ≤ j → ∀ z ∈ S,
      ell^(k-1)*‖iteratedFDeriv ℝ k b.symm z‖ ≤ T k) :
    ContDiffOn ℝ ∞ (fun z : X => f ((Data.parameterChart i.2).symm z.1,(e z.1).symm z.2)) b.target ∧
      ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k
        (fun w : X => f ((Data.parameterChart i.2).symm w.1,(e w.1).symm w.2)) z‖ ≤
          actualFastChartTransferPrefix T j*K := by
  have hg := actual_host_slice_geometry_inputs _ (hd.atlas_smooth.chart_mem i.1) _ _ _ hdata
  rcases hdata with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hphase,hback,hforward,hbj,hfj⟩
  let phi := actualSourceChartTransition (fun _ => Data.atlas.chart i.1) e
  let f0 := fun z : X => f ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm z.2)
  let f1 := fun z : X => f ((Data.parameterChart i.2).symm z.1,(e z.1).symm z.2)
  have hmap : MapsTo phi b.target (actualOriginalPrimaryNativeOpen Data nu i) :=
    fun z hz => hsource (hg.2.2.2.2.2.2.1 hz)
  have heq : EqOn f1 (f0 ∘ phi) b.target := by
    intro z hz
    change f _ = f ((Data.parameterChart i.2).symm z.1,
      (Data.atlas.chart i.1).symm (Data.atlas.chart i.1 ((e z.1).symm z.2)))
    rw [(Data.atlas.chart i.1).left_inv (hg.2.2.2.1 z hz).2]
  refine ⟨(hf.comp hg.2.2.2.2.1 hmap).congr heq,?_⟩
  intro k hk z hz
  have hgerm : f1 =ᶠ[𝓝 z] f0 ∘ phi := by
    filter_upwards [b.open_target.mem_nhds (hS hz)] with w hw
    exact heq hw
  rw [(hgerm.iteratedFDeriv ℝ k).eq_of_nhds]
  have hb := actual_fast_joint_chart_transfer T hT k phi f0 b.target
    (actualOriginalPrimaryNativeOpen Data nu i) b.open_target
    (actualOriginalPrimaryNativeOpen_isOpen Data hd nu i) hg.2.2.2.2.1 hf hmap z (hS hz)
    ell ell K hell le_rfl
    (fun r hr => hfjet r (hr.trans hk) _ (by
      dsimp only [phi]
      rw [hback (hS hz)]
      exact hsample hz))
    (fun r hr hrk => by
      dsimp only [phi]
      rw [hbj r z (hS hz)]
      exact hinvjet r hr (hrk.trans hk) z hz)
  exact hb.trans (mul_le_mul_of_nonneg_right (actualFastChartTransferCost_le_prefix T hT hk) hK)

theorem round3_original_fixed_constructed_host_normal
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (j : ℕ)
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (nu : Fin Data.primaryCount)
    (b : OpenPartialHomeomorph X X) (e : Ep → OpenPartialHomeomorph M Es)
    (hdata : ActualOriginalHostSliceData (Data.atlas.chart i.1) b
      (fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) e)
    (S : Set X) (hS : S ⊆ b.target)
    (hsource : b.source ⊆ actualOriginalNativeOpen Data i)
    (hsample : MapsTo b.symm S ((parameterTensorModelEquiv (m+1) d) ⁻¹'
      incrementsOriginalEvaluation Data.atlas Data.parameterChart
        Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i))
    (hprimary : ∀ w ∈ (actualHostAdaptedChart (Data.atlas.chart i.1) b).source,
      ((Data.parameterChart i.2).symm w.1,w.2) ∈ Data.primaryDomain nu)
    (ell budget : ℝ) (hell : 0 < ell)
    (hfinite : parameterRound2_originalFixedPacketProfile Data j ell ≠ ⊤)
    (hbudget : (parameterRound2_originalFixedPacketProfile Data j ell).toReal ≤ budget)
    (hinvjet : ∀ k, 1 ≤ k → k ≤ j → ∀ z ∈ S,
      ell^(k-1)*‖iteratedFDeriv ℝ k b.symm z‖ ≤ T k) :
    let normal := fun z : X => Data.freeNormal nu ((Data.parameterChart i.2).symm z.1,(e z.1).symm z.2)
    (ContDiffOn ℝ ∞ normal b.target ∧ ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k normal z‖ ≤
      actualFastChartTransferPrefix T j*(actualOriginalNormalJetCost (m+1) d N j*budget)) := by
  have hsource' := actual_original_host_source_primary_open Data hd i nu b e hdata hsource hprimary
  have hsample' : MapsTo b.symm S ((parameterTensorModelEquiv (m+1) d) ⁻¹'
      incrementsOriginalPrimaryEvaluation Data nu i) := by
    intro z hz
    exact ⟨hsample hz,(hsource' (b.map_target (hS hz))).1.2⟩
  have hbudget0 : 0 ≤ budget := ENNReal.toReal_nonneg.trans hbudget
  have hnormal := round3_original_fixed_normal_native_jets Data hd hs nu j ell hell hfinite budget hbudget i
  exact round3_host_original_field_jets T hT j Data hd i nu b e hdata S hS hsource' hsample'
    (Data.freeNormal nu) ell _ hell (mul_nonneg (actualOriginalNormalJetCost_nonneg _ _ _ _) hbudget0)
    hnormal.1 hnormal.2 hinvjet

#print axioms round3_original_fixed_constructed_host_normal
end GlobalEmbedding.Continuation
