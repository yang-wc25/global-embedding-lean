import Probes.ActualSecondaryObservedForcingBinding

/-!
# Exact metric error of the same constructed primary and secondary waves

The native quadratic forcing is recovered by actual inverse chart transport
and the ordinary partition. This identifies the complete metric error with
its four literal terms: primary linear residual, constructed secondary
physical residual, actual cross/self metric difference, and actual mean
defect. No error budget or cancellation identity is assumed.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open Manifold Set Function GlobalEmbedding.Paper
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {Ep Label SubPrimary : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [Fintype Label] [DecidableEq Label] [Fintype SubPrimary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ

 theorem actual_primary_quadratic_native_tensor_identity
    (phi : Label → Ep → D → ℝ) (tau : ℝ)
    (chi : Label → Ep → SubPrimary → D → ℝ) (P Q : Label → Ep → SubPrimary → D → V)
    (z : X)
    (hphi : ∀ nu, DifferentiableAt ℝ (phi nu z.1) z.2)
    (hchi : ∀ nu a, DifferentiableAt ℝ (chi nu z.1 a) z.2)
    (hP : ∀ nu a, DifferentiableAt ℝ (P nu z.1 a) z.2)
    (hQ : ∀ nu a, DifferentiableAt ℝ (Q nu z.1 a) z.2) :
    actualSpatialMetric (fderiv ℝ (fun x => actualPrimaryJointWave phi tau chi P Q (z.1,x)) z.2) +
      (∑ r ∈ actualSecondaryNonzeroRecords Label, actualSecondaryForcingTensor phi tau chi P Q r z) =
        actualPrimaryOppositeMeanTensor phi tau chi P Q z := by
  apply actual_bilinear_tensor_eq_of_basis
  intro i j
  have hh := increments_secondary_quadratic_forcing_exact phi tau chi P Q
    (fun a _ => EuclideanSpace.single a 1) z hphi hchi hP hQ i j
  have heq := congrFun (actualSecondaryNonzeroSum_eq_record_sum (fun nu mu q w =>
    (incrementsMeanPhase (incrementsSecondaryQuadraticPhase phi nu mu q w / tau) *
      incrementsSecondaryQuadraticForcing phi tau chi P Q
        (fun a _ => EuclideanSpace.single a 1) nu mu q w i j).re)) z
  dsimp only at hh
  simp only [actualSecondaryNonzeroSum] at heq
  rw [heq] at hh
  simp only [actualPrimaryJointWave, actualSecondaryForcingTensor, actualPrimaryOppositeMeanTensor,
    add_apply, sum_apply, actualRealTensorAssembly_basis, actualSpatialMetric_apply]
  linarith

 theorem actual_primary_secondary_native_grouped_identity
    (F U2 : X → V) (phi : Label → Ep → D → ℝ) (tau : ℝ)
    (chi : Label → Ep → SubPrimary → D → ℝ) (P Q : Label → Ep → SubPrimary → D → V)
    (H : X → Tensor) (delta : ℝ) (z : X)
    (hF : DifferentiableAt ℝ (fun x => F (z.1,x)) z.2)
    (hU2 : DifferentiableAt ℝ (fun x => U2 (z.1,x)) z.2)
    (hphi : ∀ nu, DifferentiableAt ℝ (phi nu z.1) z.2)
    (hchi : ∀ nu a, DifferentiableAt ℝ (chi nu z.1 a) z.2)
    (hP : ∀ nu a, DifferentiableAt ℝ (P nu z.1 a) z.2)
    (hQ : ∀ nu a, DifferentiableAt ℝ (Q nu z.1 a) z.2) :
    let U1 := actualPrimaryJointWave phi tau chi P Q
    actualFiniteMetricError F (fun y => U1 y + U2 y) H delta z =
      actualJointMetricLinearization F U1 z +
      (actualJointMetricLinearization F U2 z -
        ∑ r ∈ actualSecondaryNonzeroRecords Label, actualSecondaryForcingTensor phi tau chi P Q r z) +
      (actualSpatialMetric (fderiv ℝ (fun x => U1 (z.1,x) + U2 (z.1,x)) z.2) -
        actualSpatialMetric (fderiv ℝ (fun x => U1 (z.1,x)) z.2)) +
      (actualPrimaryOppositeMeanTensor phi tau chi P Q z - delta ^ 2 • H z) := by
  intro U1
  have hU1 : DifferentiableAt ℝ (fun x => U1 (z.1,x)) z.2 :=
    actual_primary_wave_differentiableAt (fun nu => phi nu z.1) tau (fun nu => chi nu z.1)
      (fun nu => P nu z.1) (fun nu => Q nu z.1) z.2 hphi hchi hP hQ
  have hquad := actual_primary_quadratic_native_tensor_identity phi tau chi P Q z hphi hchi hP hQ
  have hsum := (hU1.hasFDerivAt.fun_add hU2.hasFDerivAt).fderiv
  have htotal := (hF.hasFDerivAt.fun_add (hU1.hasFDerivAt.fun_add hU2.hasFDerivAt)).fderiv
  ext v w
  have hq := congrArg (fun T : Tensor => T v w) hquad
  simp only [add_apply] at hq
  simp only [actualFiniteMetricError, actualJointMetricLinearization,
    actualCoordinateMetricLinearization_apply, sub_apply, add_apply, smul_apply,
    smul_eq_mul, htotal, hsum, actualSpatialMetric_apply, inner_add_left, inner_add_right]
  dsimp only [U1] at hq ⊢
  simp only [actualSpatialMetric_apply] at hq
  linarith

variable {M SubSecondary : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype SubSecondary]
local notation "𝓙" => 𝓘(ℝ,D)

 theorem actual_constructed_secondary_original_forcing_sum
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    {n j : ℕ} {ell Mg CH delta : ℝ} {W : Set (Ep × M)}
    (data : ActualSecondarySignedRecord Label → SubSecondary →
      ActualSecondaryPhysicalPieceData F hF n j ell Mg CH delta W)
    (b : OpenPartialHomeomorph (Ep × M) X)
    (phi : Label → Ep → D → ℝ) (tau : ℝ)
    (chi : Label → Ep → SubPrimary → D → ℝ) (P Q : Label → Ep → SubPrimary → D → V)
    (binding : ∀ r : ActualSecondarySignedRecord Label,
      let H := incrementsSecondaryQuadraticForcing phi tau chi P Q
        (fun i _ => EuclideanSpace.single i 1) r.1.1.1 r.1.1.2 r.1.2
      ActualSecondaryForcingBinding F hF (fun a => (data r a).base) b
        (fun z => actualRealTensorAssembly (H z)) (fun z => actualImaginaryTensorAssembly (H z))
        (incrementsSecondaryQuadraticPhase phi r.1.1.1 r.1.1.2 r.1.2))
    (z : X) (hz : z ∈ b.target) (hzW : b.symm z ∈ W) :
    actualConstructedSecondaryForcingSum F hF data b.symm tau z =
      ∑ r ∈ actualSecondaryNonzeroRecords Label, actualSecondaryForcingTensor phi tau chi P Q r z := by
  unfold actualConstructedSecondaryForcingSum
  rw [actual_secondary_refined_sum_eq_records]
  dsimp only
  apply Finset.sum_congr rfl
  intro r hr
  have hq := (Finset.mem_filter.mp hr).2
  simp only [actualConstructedSecondaryForcingFamily, dif_pos hq]
  rw [actual_secondary_observed_forcing_partition F hF (fun a => (data ⟨r,hq⟩ a).base) b
    _ _ _ (binding ⟨r,hq⟩) tau z hz hzW]
  exact (actual_modulated_forcing_tensor_real_imag _ _).symm

 theorem actual_constructed_secondary_observed_differentiableAt
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    {n j : ℕ} {ell Mg CH delta : ℝ} {W : Set (Ep × M)}
    (data : ActualSecondarySignedRecord Label → SubSecondary →
      ActualSecondaryPhysicalPieceData F hF n j ell Mg CH delta W)
    (tau : ℝ) (length : ℕ) (hW : IsOpen W)
    (kappa : X → Ep × M) (Omega : Set X) (hOmega : IsOpen Omega)
    (hkappa : ContMDiffOn 𝓘(ℝ, X) ((𝓘(ℝ, Ep)).prod 𝓙) ∞ kappa Omega)
    (hmap : MapsTo kappa Omega W) (z : X) (hz : z ∈ Omega) :
    DifferentiableAt ℝ (fun x =>
      actualConstructedSecondarySum F hF (fun r a => (data r a).base) tau length (kappa (z.1,x))) z.2 := by
  change DifferentiableAt ℝ (fun x => actualSecondaryRefinedNonzeroSum
    (actualConstructedSecondaryFamily F hF (fun r a => (data r a).base) tau length) (kappa (z.1,x))) z.2
  rw [actual_secondary_refined_sum_eq_records]
  apply DifferentiableAt.fun_sum
  intro r hr
  apply DifferentiableAt.fun_sum
  intro a _
  have hq := (Finset.mem_filter.mp hr).2
  let d := (data ⟨r,hq⟩ a).base
  have hm := ((d.wave_regular tau length hW).1.comp hkappa hmap).contDiffOn
  have hs := actual_joint_contDiffOn_slice (d.wave tau length ∘ kappa) Omega hm z.1
  have hd := (hs.contDiffAt
    ((hOmega.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz)).differentiableAt (by simp)
  simpa only [actualConstructedSecondaryFamily, dif_pos hq, Function.comp_def] using hd

 theorem actual_constructed_complete_metric_identity
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    {n j : ℕ} {ell Mg CH delta : ℝ} {W : Set (Ep × M)}
    (data : ActualSecondarySignedRecord Label → SubSecondary →
      ActualSecondaryPhysicalPieceData F hF n j ell Mg CH delta W)
    (b : OpenPartialHomeomorph (Ep × M) X)
    (phi : Label → Ep → D → ℝ) (tau : ℝ) (length : ℕ)
    (chi : Label → Ep → SubPrimary → D → ℝ) (P Q : Label → Ep → SubPrimary → D → V)
    (binding : ∀ r : ActualSecondarySignedRecord Label,
      let H := incrementsSecondaryQuadraticForcing phi tau chi P Q
        (fun i _ => EuclideanSpace.single i 1) r.1.1.1 r.1.1.2 r.1.2
      ActualSecondaryForcingBinding F hF (fun a => (data r a).base) b
        (fun z => actualRealTensorAssembly (H z)) (fun z => actualImaginaryTensorAssembly (H z))
        (incrementsSecondaryQuadraticPhase phi r.1.1.1 r.1.1.2 r.1.2))
    (H : X → Tensor) (hW : IsOpen W)
    (Omega : Set X) (hOmega : IsOpen Omega) (hOmegaB : Omega ⊆ b.target)
    (hb : ContMDiffOn 𝓘(ℝ, X) ((𝓘(ℝ, Ep)).prod 𝓙) ∞ b.symm Omega)
    (hmap : MapsTo b.symm Omega W) (z : X) (hz : z ∈ Omega)
    (hFobs : DifferentiableAt ℝ (fun x => F (b.symm (z.1,x)).1 (b.symm (z.1,x)).2) z.2)
    (hphi : ∀ nu, DifferentiableAt ℝ (phi nu z.1) z.2)
    (hchi : ∀ nu a, DifferentiableAt ℝ (chi nu z.1 a) z.2)
    (hP : ∀ nu a, DifferentiableAt ℝ (P nu z.1 a) z.2)
    (hQ : ∀ nu a, DifferentiableAt ℝ (Q nu z.1 a) z.2) :
    let Fobs := fun y : X => F (b.symm y).1 (b.symm y).2
    let U1 := actualPrimaryJointWave phi tau chi P Q
    let U2 := actualConstructedSecondarySum F hF (fun r a => (data r a).base) tau length ∘ b.symm
    actualFiniteMetricError Fobs (fun y => U1 y + U2 y) H delta z =
      actualJointMetricLinearization Fobs U1 z +
      actualConstructedSecondaryPhysicalSum F hF data b.symm tau length z +
      (actualSpatialMetric (fderiv ℝ (fun x => U1 (z.1,x) + U2 (z.1,x)) z.2) -
        actualSpatialMetric (fderiv ℝ (fun x => U1 (z.1,x)) z.2)) +
      (actualPrimaryOppositeMeanTensor phi tau chi P Q z - delta ^ 2 • H z) := by
  intro Fobs U1 U2
  have hU2 := actual_constructed_secondary_observed_differentiableAt F hF data tau length hW
    b.symm Omega hOmega hb hmap z hz
  have heq := actual_primary_secondary_native_grouped_identity Fobs U2 phi tau chi P Q H delta z
    hFobs hU2 hphi hchi hP hQ
  have hforce := actual_constructed_secondary_original_forcing_sum F hF data b phi tau chi P Q binding z
    (hOmegaB hz) (hmap hz)
  rw [← hforce] at heq
  have hcancel := actual_constructed_secondary_linearized_cancellation F hF n j ell Mg CH delta W data
    tau length hW b.symm Omega hOmega hb hmap z hz
  change actualJointMetricLinearization Fobs U2 z -
    actualConstructedSecondaryForcingSum F hF data b.symm tau z = _ at hcancel
  rw [hcancel] at heq
  exact heq

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_primary_quadratic_native_tensor_identity
#print axioms GlobalEmbedding.Continuation.actual_primary_secondary_native_grouped_identity
#print axioms GlobalEmbedding.Continuation.actual_constructed_complete_metric_identity
