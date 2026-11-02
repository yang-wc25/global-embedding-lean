import Probes.ActualSecondaryGroupedMetricIdentity

/-!
# The literal finite metric error with its original two error scales

The actual secondary wave and physical residual budgets are produced from
primitive data inside this consumer. The cross and self terms are computed
for the same U1+U2. Only the genuine primary residual and mean defect profiles
remain as inputs from their separate original-family producers. The result
is a bound for the literal metric error, never for a replacement carrier.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Manifold Set Filter Function GlobalEmbedding.Paper
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

section Bounds
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem actual_four_joint_terms_weighted_jet
    (a b c d : X → Y) (x : X) (j : ℕ) (tau A B C D : ℝ) (htau : 0 ≤ tau)
    (ha : ContDiffAt ℝ ∞ a x) (hb : ContDiffAt ℝ ∞ b x)
    (hc : ContDiffAt ℝ ∞ c x) (hd : ContDiffAt ℝ ∞ d x)
    (hab : tau^j * ‖iteratedFDeriv ℝ j a x‖ ≤ A)
    (hbb : tau^j * ‖iteratedFDeriv ℝ j b x‖ ≤ B)
    (hcb : tau^j * ‖iteratedFDeriv ℝ j c x‖ ≤ C)
    (hdb : tau^j * ‖iteratedFDeriv ℝ j d x‖ ≤ D) :
    tau^j * ‖iteratedFDeriv ℝ j (fun y => a y+b y+c y+d y) x‖ ≤ A+B+C+D := by
  have hab' := actual_joint_slow_add_jet_bound a b j tau A B htau x
    (ha.of_le (by simp)) (hb.of_le (by simp)) hab hbb
  have habc := actual_joint_slow_add_jet_bound (fun y => a y+b y) c j tau (A+B) C htau x
    ((ha.add hb).of_le (by simp)) (hc.of_le (by simp)) hab' hcb
  exact actual_joint_slow_add_jet_bound (fun y => a y+b y+c y) d j tau (A+B+C) D htau x
    (((ha.add hb).add hc).of_le (by simp)) (hd.of_le (by simp)) habc hdb

 theorem actual_finite_increment_scale_absorption
    (delta tau ell CP CS CM CX : ℝ) (q length : ℕ)
    (hdelta : 0 ≤ delta) (hdeltatau : delta ≤ tau) (htau : 0 < tau)
    (htaul : tau ≤ ell) (hell1 : ell ≤ 1) (hql : q ≤ length)
    (hCP : 0 ≤ CP) (hCS : 0 ≤ CS) (hCM : 0 ≤ CM) (hCX : 0 ≤ CX) :
    CP*delta*tau*(tau/ell)^length + CS*(tau/ell)^length*delta^2 +
      CX*(delta^3/tau) + CM*delta^2*(tau/ell)^q ≤
        (CP+CS+CM+CX) * (delta*(tau/ell)^q+delta^3/tau) := by
  have hell : 0 < ell := htau.trans_le htaul
  have htau1 : tau ≤ 1 := htaul.trans hell1
  have hd1 : delta ≤ 1 := hdeltatau.trans htau1
  have hratio : 0 ≤ tau/ell := by positivity
  have hratio1 : tau/ell ≤ 1 := (div_le_one hell).2 htaul
  have hpow : (tau/ell)^length ≤ (tau/ell)^q :=
    pow_le_pow_of_le_one hratio hratio1 hql
  have hsquare : delta^2 ≤ delta := by nlinarith
  have hp : CP*delta*tau*(tau/ell)^length ≤ CP*delta*(tau/ell)^q := by
    calc
      _ ≤ CP*delta*1*(tau/ell)^q := by gcongr
      _ = _ := by ring
  have hs : CS*(tau/ell)^length*delta^2 ≤ CS*delta*(tau/ell)^q := by
    calc
      _ ≤ CS*(tau/ell)^q*delta := by gcongr
      _ = _ := by ring
  have hm : CM*delta^2*(tau/ell)^q ≤ CM*delta*(tau/ell)^q := by gcongr
  have hnn1 : 0 ≤ delta*(tau/ell)^q := by positivity
  have hnn2 : 0 ≤ delta^3/tau := by positivity
  nlinarith [mul_nonneg hCX hnn1, mul_nonneg (add_nonneg (add_nonneg hCP hCS) hCM) hnn2]

end Bounds

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

 theorem actual_constructed_secondary_observed_contDiffOn
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    {n j : ℕ} {ell Mg CH delta : ℝ} {W : Set (Ep × M)}
    (data : ActualSecondarySignedRecord Label → SubSecondary →
      ActualSecondaryPhysicalPieceData F hF n j ell Mg CH delta W)
    (tau : ℝ) (length : ℕ) (hW : IsOpen W)
    (kappa : X → Ep × M) (Omega : Set X)
    (hkappa : ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ kappa Omega)
    (hmap : MapsTo kappa Omega W) :
    ContDiffOn ℝ ∞ (actualConstructedSecondarySum F hF (fun r a => (data r a).base) tau length ∘ kappa) Omega := by
  change ContDiffOn ℝ ∞ (fun z => actualSecondaryRefinedNonzeroSum
    (actualConstructedSecondaryFamily F hF (fun r a => (data r a).base) tau length) (kappa z)) Omega
  rw [actual_secondary_refined_sum_eq_records]
  apply ContDiffOn.sum
  intro r hr
  apply ContDiffOn.sum
  intro a _
  have hq := (Finset.mem_filter.mp hr).2
  have hm := (((data ⟨r,hq⟩ a).base.wave_regular tau length hW).1.comp hkappa hmap).contDiffOn
  simpa only [actualConstructedSecondaryFamily, dif_pos hq, Function.comp_def] using hm

 theorem actual_finite_metric_error_contDiffOn
    (F U : X → V) (H : X → Tensor) (delta : ℝ)
    (O : Set X) (hO : IsOpen O) (hF : ContDiffOn ℝ ∞ F O)
    (hU : ContDiffOn ℝ ∞ U O) (hH : ContDiffOn ℝ ∞ H O) :
    ContDiffOn ℝ ∞ (actualFiniteMetricError F U H delta) O := by
  have hA := (incrementsJointSpatialJets_bridge (fun z => F z+U z) O hO (hF.add hU)).2.1
  have hB := (incrementsJointSpatialJets_bridge F O hO hF).2.1
  let L : (D →L[ℝ] V) →L[ℝ] (D →L[ℝ] V) →L[ℝ] Tensor := actualMetricJetPairing
  have hAA := (L.contDiff.comp_contDiffOn hA).clm_apply hA
  have hBB := (L.contDiff.comp_contDiffOn hB).clm_apply hB
  exact (hAA.sub hBB).sub (hH.const_smul (delta^2))

 def actualConstructedSecondaryWaveBudget (m N n j length L R : ℕ) (Mg CH : ℝ) (T : ℕ → ℝ) : ℝ :=
  ((4*L^2*R : ℕ) : ℝ) * actualFastChartTransferPrefix T j *
    actualSecondaryForcedWaveCost m N n length j Mg CH

 def actualConstructedSecondaryPhysicalBudget (m N n j length L R : ℕ) (Mg CH : ℝ) (T : ℕ → ℝ) : ℝ :=
  ((4*L^2*R : ℕ) : ℝ) * actualFastTensorChartTransferPrefix T j *
    actualSecondaryPhysicalCost m N n length j Mg CH

 def actualConstructedFiniteErrorCost (m N n j length L R : ℕ)
    (Mg CH M1 CP CM : ℝ) (T : ℕ → ℝ) : ℝ :=
  let M2 := actualConstructedSecondaryWaveBudget m N n (j+1) length L R Mg CH T
  CP + actualConstructedSecondaryPhysicalBudget m N n (j+1) length L R Mg CH T + CM +
    2^j*(2*M1*M2+M2^2)

 theorem actual_constructed_complete_metric_error_jets
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
    (M1 CP CM : ℝ) (hM1 : 0 ≤ M1) (hCP : 0 ≤ CP) (hCM : 0 ≤ CM) :
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
    (∀ r ≤ j, ∀ z ∈ S, tau^r*‖iteratedFDeriv ℝ r Mean z‖ ≤ CM*delta^2*(tau/ell)^q) →
    ContDiffOn ℝ ∞ (actualFiniteMetricError Fobs (fun z => U1 z+U2 z) H delta) Omega ∧
      ∀ r ≤ j, ∀ z ∈ S, tau^r*‖iteratedFDeriv ℝ r
        (actualFiniteMetricError Fobs (fun z => U1 z+U2 z) H delta) z‖ ≤
        actualConstructedFiniteErrorCost m N n j length L R Mg CH M1 CP CM T *
          (delta*(tau/ell)^q+delta^3/tau) := by
  intro Fobs U1 U2 Mean hFobs hU1 hH hlin hMean hgrouped hU1jet hlinjet hMeanjet
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
  have heq : EqOn (actualFiniteMetricError Fobs (fun z => U1 z+U2 z) H delta)
      (fun z => actualJointMetricLinearization Fobs U1 z+Secondary z+Cross z+Mean z) Omega := by
    intro z hz
    have hs := actual_joint_contDiffOn_slice Fobs Omega hFobs z.1
    have hf := (hs.contDiffAt
      ((hOmega.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz)).differentiableAt (by simp)
    have hus := actual_joint_contDiffOn_slice U1 Omega hU1 z.1
    have hu := (hus.contDiffAt
      ((hOmega.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz)).differentiableAt (by simp)
    exact actual_constructed_complete_metric_identity_of_grouped F hF data b phi tau length chi P Q binding H hW Omega
      hOmega hOmegaB hb hmap z hz hf hu (hgrouped z hz)
  refine ⟨actual_finite_metric_error_contDiffOn Fobs (fun z => U1 z+U2 z) H delta Omega hOmega hFobs
    (hU1.add hU2) hH, ?_⟩
  intro r hr z hz
  have hg := eventuallyEq_of_mem (hOmega.mem_nhds (hSOmega hz)) (fun y hy => heq hy)
  rw [(hg.iteratedFDeriv ℝ r).eq_of_nhds]
  have hsec : tau^r*‖iteratedFDeriv ℝ r Secondary z‖ ≤ CS*(tau/ell)^length*delta^2 := by
    exact hSjet r (by omega) z hz
  have hbound := actual_four_joint_terms_weighted_jet (actualJointMetricLinearization Fobs U1)
    Secondary Cross Mean z r tau _ _ _ _ htau.le
    (hlin.contDiffAt (hOmega.mem_nhds (hSOmega hz))) (hSreg z hz)
    (hCross.contDiffAt (hOmega.mem_nhds (hSOmega hz))) (hMean.contDiffAt (hOmega.mem_nhds (hSOmega hz)))
    (hlinjet r hr z hz) hsec (hCrossjet r hr z hz) (hMeanjet r hr z hz)
  exact hbound.trans (actual_finite_increment_scale_absorption delta tau ell CP CS CM
    (2^j*(2*M1*M2+M2^2)) q length hdelta hdeltatau htau htaul hell1 hql hCP hCS hCM (by positivity))

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_finite_increment_scale_absorption
#print axioms GlobalEmbedding.Continuation.actual_constructed_complete_metric_error_jets
