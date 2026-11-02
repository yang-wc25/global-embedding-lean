import IncrementsCompletion.AtScaleSecondaryRawPiece
import Probes.Round3PreparedParameterSecondaryNativeSamples
import Probes.Round3ParameterSecondaryActiveHostGeometry

/-! Actual host geometry is manufactured from positive current-scale jets.
The first forward jet uses ell^0 = 1, so no certificate at scale 1 is needed.
Every original host point, sample, cutoff, phase and reserve is retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
local notation "𝓙" => 𝓘(ℝ,D)

 theorem incrementsCompletion_at_scale_secondary_raw_from_host
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) (W : Set (Ep × M))
    (b : OpenPartialHomeomorph X X) (e : Ep → OpenPartialHomeomorph M D)
    (hdata : ActualOriginalHostSliceData (Data.atlas.chart i.1) b (actualOriginalParameterSignedPhase Data i r.val) e)
    (rho : Ep × M → ℝ) (hRho : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ rho W)
    (hSourceDomain : (actualHostAdaptedChart (Data.atlas.chart i.1) b).source ⊆ W)
    (hNative : b.source ⊆ actualOriginalNativeOpen Data i)
    (hCarrier : tsupport rho ∩ actualOriginalParameterSupportPair Data i r.val.1.1 r.val.1.2 W ⊆
      (actualHostAdaptedChart (Data.atlas.chart i.1) b).source)
    (hInner : ∀ y ∈ (actualHostAdaptedChart (Data.atlas.chart i.1) b).source, y.2 ∈ Data.atlas.inner i.1)
    (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (Tinv Kcut Tobs : ℕ → ℝ)
    (hTinv : ∀ k, 0 ≤ Tinv k) (hKcut : ∀ k, 0 ≤ Kcut k) (hTobs : ∀ k, 0 ≤ Tobs k)
    (hProfiles : ∀ observer k, 1 ≤ k → ∀ z,
      parameterTensorModelEquiv (m+1) d z ∈ incrementsOriginalEvaluation Data.atlas Data.parameterChart
        Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet (observer,i.2) →
      (z.1,(Data.atlas.chart observer).symm z.2) ∈
        tsupport rho ∩ actualOriginalParameterSupportPair Data i r.val.1.1 r.val.1.2 W →
      let t := ((OpenPartialHomeomorph.refl Ep).prod (Data.atlas.chart observer)).symm.trans
        (actualHostAdaptedChart (Data.atlas.chart i.1) b)
      ell^(k-1)*‖iteratedFDeriv ℝ k t z‖ ≤ Tobs k ∧
        ell^(k-1)*‖iteratedFDeriv ℝ k t.symm (t z)‖ ≤ Tinv k)
    (hCut : ∀ n k, k ≤ n → ∀ z,
      parameterTensorModelEquiv (m+1) d z ∈ incrementsOriginalEvaluation Data.atlas Data.parameterChart
        Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i →
      ell^k*‖iteratedFDeriv ℝ k (fun y : X => rho (y.1,(Data.atlas.chart i.1).symm y.2)) z‖ ≤ Kcut n)
    (cT : ℝ) (hcT : 0 < cT)
    (hFrame : ∀ z ∈ b.target, ∀ v : Tdata, cT*‖v‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame
        (actualOriginalOpenParameterSlice Data i z.1)
        (actualOriginalOpenParameterSlice_contMDiff Data hd hs i z.1) (e z.1).symm z.2 v‖^2) :
    ∃ out : IncrementsCompletionAtScaleSecondaryRawPiece Data hd hs i r W ell
      (fun observer : Fin Data.atlas.count => Data.atlas.chart observer)
      (fun observer => (parameterTensorModelEquiv (m+1) d) ⁻¹'
        incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet (observer,i.2)),
      out.choice = ⟨Data.atlas.chart i.1,actualHostAdaptedChart (Data.atlas.chart i.1) b,
        (fun p x => (e p).symm x),rho⟩ ∧
      out.Tinv = Tinv ∧ out.Kcut = Kcut ∧ out.Tobs = Tobs ∧ out.cT = cT ∧ out.Bnative = 1+Tobs 1 := by
  let a := actualHostAdaptedChart (Data.atlas.chart i.1) b
  let q := actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)
  let carrier := tsupport rho ∩ actualOriginalParameterSupportPair Data i r.val.1.1 r.val.1.2 W
  let S := round3PreparedParameterSecondarySample Data i a carrier
  have hNS := (actual_host_slice_geometry_inputs (Data.atlas.chart i.1)
    (hd.atlas_smooth.chart_mem i.1) b _ e hdata).1
  have hTransition := round3_prepared_host_transition_domains (Data.atlas.chart i.1) b hNS
  have hTransitionJets := round3_prepared_host_transition_jets (Data.atlas.chart i.1) b hNS
  obtain ⟨hS,hSample,hHostSample,hObsSample⟩ := round3_prepared_parameter_secondary_native_samples
    Data hd i b e _ hdata carrier hCarrier (fun y hy => hInner y (hCarrier hy))
  have hInvSmooth := (round3Parameter_native_observer_transition_smooth a hdata.2.1 hdata.2.2.1
    (Data.atlas.chart i.1) (hd.atlas_smooth.chart_mem i.1)).2
  have hqInv : ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ q.symm q.target :=
    contDiff_fst.contMDiff.contMDiffOn.prodMk
      ((contMDiffOn_symm_of_mem_maximalAtlas (hd.atlas_smooth.chart_mem i.1)).comp
        contDiff_snd.contMDiff.contMDiffOn (fun _ hz => hz.2))
  have hCutSmooth : ContDiffOn ℝ ∞ (rho ∘ q.symm) (q.symm.trans a).source :=
    (hRho.comp (hqInv.mono inter_subset_left) (fun _ hz => hSourceDomain hz.2)).contDiffOn
  have hClosed : IsClosed (Subtype.val ⁻¹' carrier : Set W) :=
    ((isClosed_tsupport rho).preimage continuous_subtype_val).inter
      ((actual_relative_support_preimage_closed W (fun z => Data.cutoff r.val.1.1 ((Data.parameterChart i.2).symm z.1,z.2))).inter
        (actual_relative_support_preimage_closed W (fun z => Data.cutoff r.val.1.2 ((Data.parameterChart i.2).symm z.1,z.2))))
  have hRel : tsupport (fun y : W => rho y.val) ⊆ Subtype.val ⁻¹' tsupport rho := by
    apply closure_minimal _ ((isClosed_tsupport rho).preimage continuous_subtype_val)
    intro y hy
    exact subset_tsupport rho hy
  have hInverse : ∀ k, 1 ≤ k → ∀ z, z ∈ S →
      ell^(k-1)*‖iteratedFDeriv ℝ k (q.symm.trans a).symm z‖ ≤ Tinv k := by
    intro k hk z hz
    obtain ⟨y,hy,rfl⟩ := hz
    have hqleft : q.symm (q y) = y := q.left_inv (hCarrier hy.1).1
    have hh := (hProfiles i.1 k hk (q y) hy.2 (by
      change q.symm (q y) ∈ carrier
      rw [hqleft]
      exact hy.1)).2
    have heq : (q.symm.trans a) (q y) = a y := congrArg a hqleft
    change ell^(k-1)*‖iteratedFDeriv ℝ k (q.symm.trans a).symm ((q.symm.trans a) (q y))‖ ≤ Tinv k at hh
    rwa [heq] at hh
  have hFirst : ∀ z ∈ S, ‖fderiv ℝ b (b.symm z)‖ ≤ 1+Tobs 1 := by
    intro z hz
    obtain ⟨y,hy,rfl⟩ := hz
    have hqleft : q.symm (q y) = y := q.left_inv (hCarrier hy.1).1
    have hh := (hProfiles i.1 1 le_rfl (q y) hy.2 (by
      change q.symm (q y) ∈ carrier
      rw [hqleft]
      exact hy.1)).1
    change ell^(1-1)*‖iteratedFDeriv ℝ 1 (q.symm.trans a) (q y)‖ ≤ Tobs 1 at hh
    have hj := hTransitionJets.1 1 (q y) (hCarrier hy.1).2
    change iteratedFDeriv ℝ 1 (q.symm.trans a) (q y) = iteratedFDeriv ℝ 1 b (q y) at hj
    rw [hj] at hh
    simp only [Nat.sub_self,pow_zero,one_mul,norm_iteratedFDeriv_one] at hh
    change ‖fderiv ℝ b (b.symm (b (q y)))‖ ≤ _
    have hleft : b.symm (b (q y)) = q y := b.left_inv (hCarrier hy.1).2
    rw [hleft]
    exact hh.trans (by linarith)
  let out : IncrementsCompletionAtScaleSecondaryRawPiece Data hd hs i r W ell
      (fun observer : Fin Data.atlas.count => Data.atlas.chart observer)
      (fun observer => (parameterTensorModelEquiv (m+1) d) ⁻¹'
        incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet (observer,i.2)) := {
    choice := ⟨Data.atlas.chart i.1,a,(fun p x => (e p).symm x),rho⟩
    carrier := carrier
    sample := S
    host_eq := rfl
    cutoff_smooth := hRho
    carrier_eq := rfl
    sample_subset := by rw [hdata.1]; exact hS
    carrier_source := hCarrier
    source_domain := hSourceDomain
    chart_smooth := hdata.2.1
    chart_inverse_smooth := hdata.2.2.1
    host_source := fun _ hz => hz.1
    support := fun _ hz => ⟨hRel hz.1,hz.2⟩
    pair := inter_subset_right
    cut_smooth := hCutSmooth
    inv_smooth := hInvSmooth
    host_samples := hHostSample
    observer_samples := fun v z hz => hObsSample v z hz.1 hz.2
    Tinv := Tinv
    Kcut := Kcut
    Tobs := Tobs
    Tinv_nonneg := hTinv
    Kcut_nonneg := hKcut
    Tobs_nonneg := hTobs
    cut_jets := fun n k hk z hz => hCut n k hk _ (hHostSample ⟨z,hz,rfl⟩)
    inv_jets := hInverse
    observer_jets := fun v z hz k hk => (hProfiles v k hk z hz.1 hz.2).1
    cT := cT
    Bnative := 1+Tobs 1
    cT_pos := hcT
    Bnative_pos := by linarith [hTobs 1]
    produce := by
      intro n j budget c hell hell1 hEll hfinite hbudget
      obtain ⟨geom,hc,hchart,hphase,hsample,hsupport,_⟩ :=
        round3Parameter_secondary_geometry_from_active_host Data hd hs hImm i r.val.1.1 b e
          (actualOriginalParameterSignedPhase Data i r.val) hdata carrier W hClosed hCarrier hSourceDomain hNative
          n j Tinv hTinv S hS hSample ell budget c cT (1+Tobs 1) hell hell1 hEll hcT
          (by linarith [hTobs 1]) hfinite hbudget hFirst hFrame (by
            intro k hk hkj z hz
            rw [← hTransitionJets.2 k z (hS hz)]
            exact hInverse k hk z hz)
      exact ⟨geom,hc,hchart,hphase,hsample,hsupport⟩ }
  exact ⟨out,rfl,rfl,rfl,rfl,rfl,rfl⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_at_scale_secondary_raw_from_host
