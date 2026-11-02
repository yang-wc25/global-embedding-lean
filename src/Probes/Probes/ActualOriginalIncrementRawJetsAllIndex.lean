import Smoothing.ParameterRound2PrimaryRawIndex
import Smoothing.ParameterRound2PhysicalCoefficientIndex
import Probes.ActualSecondaryRawMetricData
import Probes.ActualSecondaryOriginalRawFamilyAllIndex

/-! The SAME literal original U1+U2 has its displacement budget produced
from actual raw profiles, fixed choices and original local counts. All output
wave/source/correction budgets are derived internally. The map is independent
of the observation order and observer. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m N : ℕ} {Ep M Tr : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ
private local instance rawDataTensorSemi : SeminormedAddCommGroup Tensor := ContinuousLinearMap.toSeminormedAddCommGroup
private local instance rawDataTensorNormed : NormedAddCommGroup Tensor := ContinuousLinearMap.toNormedAddCommGroup
private local instance rawDataTensorSpace : NormedSpace ℝ Tensor := ContinuousLinearMap.toNormedSpace

 theorem actual_original_increment_raw_jets_uniform_all_index
    (nInput nSolve j q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (hSolve : j+2+(q+2) ≤ nSolve) (hInput : nSolve+2+(q+2) ≤ nInput)
    (reserve Bnd Mg Kcut : ℝ) (hc : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (T Tinv Tobs : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k) :
    ∃ CR : ℝ, 0 ≤ CR ∧ ∀ (Label SubPrimary SubSecondary : Type*)
      [Fintype Label] [DecidableEq Label] [Fintype SubPrimary] [Fintype SubSecondary], ∀
      (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
      (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
      (input inputbar : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
      (W : Set (Ep × M)) (primary : Label → Set (Ep × M)) (ell delta tau Delta : ℝ)
      (_hdelta : 0 ≤ delta) (_hdeltatau : delta ≤ tau)
      (choice : ActualSecondarySignedRecord Label → SubSecondary → ActualOriginalSecondaryChoice Ep M m)
      (raw : ActualOriginalSecondaryRawData (Tr := Tr) F hF g input inputbar nInput nSolve j q Rsub Lprimary
        reserve Bnd Mg Kcut T Tinv W primary ell delta tau Delta choice)
      (e : OpenPartialHomeomorph M D) (Omega S : Set X)
      (_obs : ActualOriginalSecondaryObservationData raw Tobs Rsecondary e Omega S),
    let U := actualOriginalIncrementMap F hF g input (q+2) tau delta choice
    ContDiffOn ℝ ∞ (fun z : X => U (z.1,e.symm z.2)) Omega ∧
      ∀ k ≤ j+1, ∀ z ∈ S, tau^k*‖iteratedFDeriv ℝ k
        (fun w : X => U (w.1,e.symm w.2)) z‖ ≤ CR*delta*tau := by
  obtain ⟨CH,hCH,hFamily⟩ := actual_original_secondary_family_from_raw_uniform_all_index
    (m := m) (N := N) (Ep := Ep) (M := M) (Tr := Tr)
    nInput nSolve q Rsub Lprimary hq hInput
    reserve Bnd Mg Kcut hc hBnd hMg hKcut T Tinv hT hTinv
  obtain ⟨CU,CP,hCU,_hCP,hPrimary⟩ := parameterRound2_original_primary_consumers_from_raw_index
    (m := m) (N := N) (Ep := Ep) (M := M) (Tr := Tr)
    nInput (q+2) j Rsub Lprimary (by omega) reserve Bnd Mg hc hBnd hMg T hT
  let C2 := actualConstructedSecondaryWaveBudget m N nSolve (j+1) (q+2)
    Lprimary Rsecondary Mg CH Tobs
  have hC2 : 0 ≤ C2 := by
    have hW := actualSecondaryForcedWaveCost_nonneg m N nSolve (q+2) (j+1) Mg CH hMg hCH
    have hT0 := actualFastChartTransferPrefix_nonneg Tobs hTobs (j+1)
    dsimp only [C2,actualConstructedSecondaryWaveBudget]
    positivity
  refine ⟨CU+C2,add_nonneg hCU hC2,?_⟩
  intro Label SubPrimary SubSecondary _ _ _ _ F hF g input inputbar W primary ell delta tau Delta hdelta hdeltatau choice raw e Omega S obs U
  obtain ⟨data,hd,hsum⟩ := hFamily Label SubPrimary SubSecondary F hF g input inputbar W primary (j+1) ell delta tau Delta choice raw.geometry
    raw.coordinate raw.chart raw.phase raw.host raw.hostInverse raw.hostSource raw.cutoffSupport
    raw.cutoffSmooth raw.inverseSmooth raw.hostProfiles raw.cutoffJets raw.inverseJets
  have hchart (r) (a) : (data r a).base.chart = (raw.geometry r a).chart :=
    (hd r a).2.1.trans (raw.chart r a).symm
  have hsupp (r) (a) : (data r a).base.support = (raw.geometry r a).support := (hd r a).2.2.2.1
  have hsample (r) (a) : (data r a).base.sample = (raw.geometry r a).sample := (hd r a).2.2.2.2.1
  let b := (OpenPartialHomeomorph.refl Ep).prod e
  have hbFun : (b.symm : X → Ep × M) = (fun z : X => (z.1,e.symm z.2)) := rfl
  have hb : ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ b.symm Omega := by
    have hf0 : ContMDiffOn 𝓘(ℝ,X) 𝓘(ℝ,Ep) ∞ (fun z : X => z.1) Omega := contDiffOn_fst.contMDiffOn
    have hs0 : ContMDiffOn 𝓘(ℝ,X) 𝓙 ∞ (fun z : X => z.2) Omega := contDiffOn_snd.contMDiffOn
    exact hf0.prodMk (obs.inverse.comp hs0 (fun z hz => obs.target z hz))
  have hobsB : Omega ⊆ b.target := fun z hz => ⟨Set.mem_univ _,obs.target z hz⟩
  have ht : ∀ r a, ContDiffOn ℝ ∞ ((data r a).base.chart ∘ b.symm) (obs.domains r a) := by
    intro r a
    rw [hchart]
    exact (obs.transition r a).mono (fun z hz => ⟨hobsB (obs.domainsSubset r a hz),obs.source r a hz⟩)
  have hp := hPrimary F hF g input inputbar W primary e Omega S tau ell Delta obs.profiles raw.primaryGeometry delta
  have hu2 := actual_constructed_secondary_observed_contDiffOn F hF data tau (q+2)
    obs.profiles.prim.hW b.symm Omega hb obs.profiles.hmapWO
  obtain ⟨_hs2,hj2⟩ := actual_constructed_secondary_sum_weighted_jets F hF
    (fun r a => (data r a).base) tau (q+2) (by omega)
    (obs.profiles.htau.trans_le obs.profiles.htaul) obs.profiles.hell1
    obs.profiles.htau obs.profiles.htaul hMg hCH obs.profiles.prim.hW
    (fun nu => incrementsGlobalRelativeSupport W (g.cutoff nu))
    (fun r a => by rw [hsupp]; exact raw.pairSupport r a)
    b.symm Omega S obs.profiles.hO obs.profiles.hSO hb.continuousOn obs.profiles.hmapWO
    obs.domains obs.openDomains (fun r a => by simpa only [hsupp,hbFun] using obs.activeDomains r a)
    (fun r a => by simpa only [hchart,hbFun] using obs.source r a) ht Tobs hTobs
    (fun r a z hz => by simpa only [hchart,hsample,hbFun] using obs.samples r a z (by simpa only [hsupp,hbFun] using hz))
    (fun r a z hz k hk hkj => by
      simpa only [hchart,hbFun] using obs.transitionJets r a z (by simpa only [hsupp,hbFun] using hz) k hk (by omega))
    Lprimary Rsecondary obs.profiles.hCount
    (fun r z hz => by simpa only [hsupp,hbFun] using obs.localCount r z hz)
  let U1 := fun z : X => delta • incrementsGlobalPrimaryWave F hF g input (q+2) tau (z.1,e.symm z.2)
  let U2 := actualConstructedSecondarySum F hF (fun r a => (data r a).base) tau (q+2) ∘ b.symm
  have heq : (fun z : X => U (z.1,e.symm z.2)) = fun z => U1 z+U2 z := by
    funext z
    simp only [U,actualOriginalIncrementMap,U1,U2,Function.comp_apply,hsum,b]
    rfl
  rw [heq]
  refine ⟨hp.1.add hu2,?_⟩
  intro k hk z hz
  have hfirst : tau^k*‖iteratedFDeriv ℝ k U1 z‖ ≤ CU*delta*tau := by
    simpa only [abs_of_nonneg hdelta] using hp.2.2.1 k hk z hz
  have hsecond : tau^k*‖iteratedFDeriv ℝ k U2 z‖ ≤ C2*delta^2 := hj2 k hk z hz
  have hsumj := actual_joint_slow_add_jet_bound U1 U2 k tau (CU*delta*tau) (C2*delta^2)
    obs.profiles.htau.le z
    ((hp.1.contDiffAt (obs.profiles.hO.mem_nhds (obs.profiles.hSO hz))).of_le (by simp))
    ((hu2.contDiffAt (obs.profiles.hO.mem_nhds (obs.profiles.hSO hz))).of_le (by simp)) hfirst hsecond
  apply hsumj.trans
  have hmul := mul_le_mul_of_nonneg_left hdeltatau hdelta
  have hc := mul_le_mul_of_nonneg_left hmul hC2
  nlinarith

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_increment_raw_jets_uniform_all_index
