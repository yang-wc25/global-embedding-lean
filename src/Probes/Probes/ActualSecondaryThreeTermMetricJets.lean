import Probes.ActualSecondaryCompleteMetricJets

/-! The actual finite metric error after subtracting its SAME original native
mean defect. The primary residual, constructed secondary physical residual,
and actual U1/U2 cross/self metric terms are all estimated before the finite
mean iteration is inserted in the original atlas norm. No mean norm or mean
jet estimate is required by this theorem. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open Manifold Set Filter Function GlobalEmbedding.Paper
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m N : ℕ} {Ep M Label SubPrimary SubSecondary : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Label] [DecidableEq Label] [Fintype SubPrimary] [Fintype SubSecondary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ

private local instance completeTensorSemi : SeminormedAddCommGroup Tensor :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance completeTensorNormed : NormedAddCommGroup Tensor :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance completeTensorSpace : NormedSpace ℝ Tensor :=
  ContinuousLinearMap.toNormedSpace
private local instance completePartialSemi : SeminormedAddCommGroup ((D →L[ℝ] V) →L[ℝ] Tensor) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance completePartialNormed : NormedAddCommGroup ((D →L[ℝ] V) →L[ℝ] Tensor) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance completePartialSpace : NormedSpace ℝ ((D →L[ℝ] V) →L[ℝ] Tensor) :=
  ContinuousLinearMap.toNormedSpace

 theorem actual_constructed_metric_error_without_mean_jets
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (n j q length : ℕ) (ell Mg CH delta tau : ℝ) (W : Set (Ep × M))
    (data : ActualSecondarySignedRecord Label → SubSecondary →
      ActualSecondaryPhysicalPieceData F hF n (j+1) ell Mg CH delta W)
    (hbudget : j+2+length ≤ n) (hql : q ≤ length)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (htau : 0 < tau) (htaul : tau ≤ ell)
    (hdelta : 0 ≤ delta) (hdeltatau : delta ≤ tau) (hMg : 0 ≤ Mg) (hCH : 0 ≤ CH) (hW : IsOpen W)
    (b : OpenPartialHomeomorph (Ep × M) X)
    (phi : Label → Ep → D → ℝ) (chi : Label → Ep → SubPrimary → D → ℝ)
    (P Q : Label → Ep → SubPrimary → D → V)
    (binding : ∀ r : ActualSecondarySignedRecord Label,
      let H := incrementsSecondaryQuadraticForcing phi tau chi P Q
        (fun i _ => EuclideanSpace.single i 1) r.1.1.1 r.1.1.2 r.1.2
      ActualSecondaryForcingBinding F hF (fun a => (data r a).base) b
        (fun z => actualRealTensorAssembly (H z)) (fun z => actualImaginaryTensorAssembly (H z))
        (incrementsSecondaryQuadraticPhase phi r.1.1.1 r.1.1.2 r.1.2))
    (H : X → Tensor) (K : Label → Set (Ep × M))
    (hprimary : ∀ r a, (data r a).base.support ⊆ K r.val.1.1 ∩ K r.val.1.2)
    (Omega S : Set X) (hOmega : IsOpen Omega) (hSOmega : S ⊆ Omega) (hOmegaB : Omega ⊆ b.target)
    (hb : ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ b.symm Omega)
    (hmap : MapsTo b.symm Omega W) (hfirst : ∀ z ∈ Omega, (b.symm z).1 = z.1)
    (O : ActualSecondarySignedRecord Label → SubSecondary → Set X)
    (hO : ∀ r a, IsOpen (O r a)) (hOOmega : ∀ r a, O r a ⊆ Omega)
    (hactiveO : ∀ r a, S ∩ b.symm ⁻¹' (data r a).base.support ⊆ O r a)
    (hsource : ∀ r a, MapsTo b.symm (O r a) (data r a).base.chart.source)
    (htransition : ∀ r a, ContDiffOn ℝ ∞ ((data r a).base.chart ∘ b.symm) (O r a))
    (T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i)
    (hsample : ∀ r a z, z ∈ S ∩ b.symm ⁻¹' (data r a).base.support →
      (data r a).base.chart (b.symm z) ∈ (data r a).base.sample)
    (htransitionb : ∀ r a z, z ∈ S ∩ b.symm ⁻¹' (data r a).base.support →
      ∀ i, 1 ≤ i → i ≤ j+2 →
        ell^(i-1)*‖iteratedFDeriv ℝ i ((data r a).base.chart ∘ b.symm) z‖ ≤ T i)
    (L R : ℕ)
    (hL : ∀ z ∈ S, (Finset.univ.filter (fun nu => b.symm z ∈ K nu)).card ≤ L)
    (hR : ∀ r : ActualSecondarySignedRecord Label, ∀ z ∈ S,
      (Finset.univ.filter (fun a => b.symm z ∈ (data r a).base.support)).card ≤ R)
    (M1 CP : ℝ) (hM1 : 0 ≤ M1) (hCP : 0 ≤ CP) :
    let Fobs := fun z : X => F (b.symm z).1 (b.symm z).2
    let U1 := actualPrimaryJointWave phi tau chi P Q
    let U2 := actualConstructedSecondarySum F hF (fun r a => (data r a).base) tau length ∘ b.symm
    let Mean := fun z => actualPrimaryOppositeMeanTensor phi tau chi P Q z - delta^2 • H z
    ContDiffOn ℝ ∞ Fobs Omega → ContDiffOn ℝ ∞ U1 Omega → ContDiffOn ℝ ∞ H Omega →
    ContDiffOn ℝ ∞ (actualJointMetricLinearization Fobs U1) Omega → ContDiffOn ℝ ∞ Mean Omega →
    (∀ z ∈ Omega, ∀ i, fderiv ℝ (fun x => U1 (z.1,x)) z.2 (EuclideanSpace.single i 1) =
      incrementsGroupedRealDerivative (fun nu => phi nu z.1 z.2 / tau)
        (incrementsSecondaryPhysicalCoefficient phi tau chi P Q
          (fun r _ => EuclideanSpace.single r 1) z) i) →
    (∀ r ≤ j+1, ∀ z ∈ S, tau^r*‖iteratedFDeriv ℝ r U1 z‖ ≤ M1*delta*tau) →
    (∀ r ≤ j, ∀ z ∈ S, tau^r*‖iteratedFDeriv ℝ r (actualJointMetricLinearization Fobs U1) z‖ ≤
      CP*delta*tau*(tau/ell)^length) →
    ContDiffOn ℝ ∞ (fun z => actualFiniteMetricError Fobs (fun w => U1 w+U2 w) H delta z - Mean z) Omega ∧
      ∀ r ≤ j, ∀ z ∈ S, tau^r*‖iteratedFDeriv ℝ r
        (fun z => actualFiniteMetricError Fobs (fun w => U1 w+U2 w) H delta z - Mean z) z‖ ≤
        actualConstructedFiniteErrorCost m N n j length L R Mg CH M1 CP 0 T *
          (delta*(tau/ell)^q+delta^3/tau) := by
  intro Fobs U1 U2 Mean hFobs hU1 hH hlin hMean hgrouped hU1jet hlinjet
  let M2 := actualConstructedSecondaryWaveBudget m N n (j+1) length L R Mg CH T
  let CS := actualConstructedSecondaryPhysicalBudget m N n (j+1) length L R Mg CH T
  have hWcost := actualSecondaryForcedWaveCost_nonneg m N n length (j+1) Mg CH hMg hCH
  have hPcost := actualSecondaryPhysicalCost_nonneg m N n length (j+1) Mg CH hMg hCH
  have hVprefix := actualFastChartTransferPrefix_nonneg T hT (j+1)
  have hTprefix := actualFastTensorChartTransferPrefix_nonneg T hT (j+1)
  have hM2 : 0 ≤ M2 := by dsimp [M2, actualConstructedSecondaryWaveBudget]; positivity
  have hCS : 0 ≤ CS := by dsimp [CS, actualConstructedSecondaryPhysicalBudget]; positivity
  have hU2 := actual_constructed_secondary_observed_contDiffOn F hF data tau length hW b.symm Omega hb hmap
  obtain ⟨_hwreg, hwjet⟩ := actual_constructed_secondary_sum_weighted_jets F hF
    (fun r a => (data r a).base) tau length (by omega) hell hell1 htau htaul hMg hCH hW K hprimary
    b.symm Omega S hOmega hSOmega hb.continuousOn hmap O hO hactiveO hsource htransition T hT hsample
    (fun r a z hz i hi hij => htransitionb r a z hz i hi (by omega)) L R hL hR
  have hwjet' : ∀ r ≤ j+1, ∀ z ∈ S, tau^r*‖iteratedFDeriv ℝ r U2 z‖ ≤ M2*delta^2 := by
    intro r hr z hz
    exact hwjet r hr z hz
  obtain ⟨hSreg, hSjet⟩ := actual_constructed_secondary_physical_sum_weighted_jets F hF n (j+1) ell Mg CH delta W
    data tau length (by omega) hell hell1 htau htaul hMg hCH hW K hprimary b.symm Omega S hOmega hSOmega
    hb.continuousOn hmap hfirst O hO hOOmega hactiveO hsource htransition T hT hsample htransitionb L R hL hR
  let Secondary := actualConstructedSecondaryPhysicalSum F hF data b.symm tau length
  let Cross := fun z : X => actualSpatialMetric (fderiv ℝ (fun x => U1 (z.1,x)+U2 (z.1,x)) z.2) -
    actualSpatialMetric (fderiv ℝ (fun x => U1 (z.1,x)) z.2)
  obtain ⟨hCross, hCrossjet⟩ := actual_secondary_metric_remainder_weighted_jets U1 U2 Omega S hOmega hSOmega
    hU1 hU2 j tau delta M1 M2 htau hdelta hdeltatau hM1 hM2 hU1jet hwjet'
  have heq : EqOn (fun z => actualFiniteMetricError Fobs (fun w => U1 w+U2 w) H delta z-Mean z)
      (fun z => actualJointMetricLinearization Fobs U1 z+Secondary z+Cross z) Omega := by
    intro z hz
    have hs := actual_joint_contDiffOn_slice Fobs Omega hFobs z.1
    have hf := (hs.contDiffAt
      ((hOmega.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz)).differentiableAt (by simp)
    have hus := actual_joint_contDiffOn_slice U1 Omega hU1 z.1
    have hu := (hus.contDiffAt
      ((hOmega.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz)).differentiableAt (by simp)
    have hh := actual_constructed_complete_metric_identity_of_grouped F hF data b phi tau length chi P Q binding H hW Omega
      hOmega hOmegaB hb hmap z hz hf hu (hgrouped z hz)
    change actualFiniteMetricError Fobs (fun w => U1 w+U2 w) H delta z =
      actualJointMetricLinearization Fobs U1 z+Secondary z+Cross z+Mean z at hh
    dsimp only
    rw [hh]
    abel
  refine ⟨(actual_finite_metric_error_contDiffOn Fobs (fun z => U1 z+U2 z) H delta Omega hOmega hFobs
    (hU1.add hU2) hH).sub hMean, ?_⟩
  intro r hr z hz
  have hg := eventuallyEq_of_mem (hOmega.mem_nhds (hSOmega hz)) (fun y hy => heq hy)
  rw [(hg.iteratedFDeriv ℝ r).eq_of_nhds]
  have hsec : tau^r*‖iteratedFDeriv ℝ r Secondary z‖ ≤ CS*(tau/ell)^length*delta^2 := by
    exact hSjet r (by omega) z hz
  have hab := actual_joint_slow_add_jet_bound (actualJointMetricLinearization Fobs U1)
    Secondary r tau (CP*delta*tau*(tau/ell)^length) (CS*(tau/ell)^length*delta^2) htau.le z
    ((hlin.contDiffAt (hOmega.mem_nhds (hSOmega hz))).of_le (by simp))
    ((hSreg z hz).of_le (by simp)) (hlinjet r hr z hz) hsec
  have hbound := actual_joint_slow_add_jet_bound
    (fun w => actualJointMetricLinearization Fobs U1 w+Secondary w) Cross r tau
    (CP*delta*tau*(tau/ell)^length+CS*(tau/ell)^length*delta^2)
    (2^j*(2*M1*M2+M2^2)*(delta^3/tau)) htau.le z
    (((hlin.contDiffAt (hOmega.mem_nhds (hSOmega hz))).add (hSreg z hz)).of_le (by simp))
    ((hCross.contDiffAt (hOmega.mem_nhds (hSOmega hz))).of_le (by simp)) hab (hCrossjet r hr z hz)
  have hscale := actual_finite_increment_scale_absorption delta tau ell CP CS 0
    (2^j*(2*M1*M2+M2^2)) q length hdelta hdeltatau htau htaul hell1 hql hCP hCS (by simp) (by positivity)
  simp only [zero_mul,add_zero] at hscale
  exact hbound.trans (by
    simpa only [actualConstructedFiniteErrorCost,add_zero,M2,CS] using hscale)


end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_constructed_metric_error_without_mean_jets
