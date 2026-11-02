import NormalPolar.ParameterDisplacementPrimaryJointGrouped
import Probes.Round4ActualProbeCoefficientJets
import Probes.Round4PrescribedObservedZeroGerm
import Probes.ActualSecondaryOppositeRegularity

/-! The actual physical derivative coefficient is smooth on the full original
observation domain. Active phases are differentiated only on their own open
neighborhoods; relative support gives a zero germ for every inactive complete
amplitude and hence for its actual coefficient. This produces the opposite-mean
regularity from the same array, without a mean-regularity hypothesis. -/

noncomputable section
open Set Filter Function GlobalEmbedding.Paper
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

/-- Qualitative regularity for the literal coefficient, retaining its true
spatial derivative and phase quotient. No derivative budget is needed. -/
theorem actualRepairModelFirstDefect_coefficient_contDiffOn
    (R Q : X → V) (phi : X → ℝ) (tau : ℝ) (v : D) (co : Fin N)
    (O : Set X) (hO : IsOpen O) (hR : ContDiffOn ℝ ∞ R O)
    (hQ : ContDiffOn ℝ ∞ Q O) (hphi : ContDiffOn ℝ ∞ phi O) :
    ContDiffOn ℝ ∞ (fun z : X => incrementsPrimaryDerivativeCoefficient
      (fun x => phi (z.1,x)) tau (fun (_ : Unit) _ => 1)
      (fun _ x => R (z.1,x)) (fun _ x => Q (z.1,x)) z.2 v co) O := by
  let ev := incrementsFreeComplexCoordinate co
  let C := fun z : X => ev (R z)+Complex.I • ev (Q z)
  let grad := fun z : X => fderiv ℝ (fun x => phi (z.1,x)) z.2 v
  let dC := fun z : X => fderiv ℝ (fun x => C (z.1,x)) z.2 v
  let fast := fun z : X => tau⁻¹ • actualJointPhaseProduct (grad z) (C z)
  have hRe : ContDiffOn ℝ ∞ (fun z => ev (R z)) O := ev.contDiff.comp_contDiffOn hR
  have hQe : ContDiffOn ℝ ∞ (fun z => ev (Q z)) O := ev.contDiff.comp_contDiffOn hQ
  have hC : ContDiffOn ℝ ∞ C O := hRe.add (hQe.const_smul Complex.I)
  have hdC : ContDiffOn ℝ ∞ dC O :=
    ((incrementsJointSpatialJets_bridge C O hO hC).2.1).clm_apply contDiffOn_const
  have hgrad : ContDiffOn ℝ ∞ grad O :=
    ((incrementsJointSpatialJets_bridge phi O hO hphi).2.1).clm_apply contDiffOn_const
  have hprod : ContDiffOn ℝ ∞ (fun z : X => actualJointPhaseProduct (grad z) (C z)) O :=
    (actualJointPhaseProduct.contDiff.comp_contDiffOn hgrad).clm_apply hC
  have hfast : ContDiffOn ℝ ∞ fast O := hprod.const_smul tau⁻¹
  apply (hdC.add hfast).congr
  intro z hz
  have hRs := (actual_joint_contDiffOn_slice R O hR z.1).contDiffAt
    ((hO.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz)
  have hQs := (actual_joint_contDiffOn_slice Q O hQ z.1).contDiffAt
    ((hO.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz)
  have hc := increments_primary_correction_coefficient_eq (fun x => phi (z.1,x)) tau
    (fun (_ : Unit) x => R (z.1,x)) (fun (_ : Unit) x => Q (z.1,x)) z.2 v co
    (fun _ => hRs.differentiableAt (by simp)) (fun _ => hQs.differentiableAt (by simp))
  have hsum : incrementsPrimaryCorrectionSum (fun (_ : Unit) x => R (z.1,x))
      (fun (_ : Unit) x => Q (z.1,x)) co = fun x => C (z.1,x) := by
    funext x
    simp [incrementsPrimaryCorrectionSum,C,ev]
  rw [hsum] at hc
  change _ = dC z+fast z
  rw [hc]
  congr 1
  rw [show fast z = tau⁻¹ • actualJointPhaseProduct (grad z) (C z) from rfl,
    actualJointPhaseProduct_apply,Complex.real_smul]
  dsimp only [grad]
  push_cast
  ring

/-- Actual support, active phase regularity and the already constructed
complete amplitudes supply the full physical coefficient regularity. -/
theorem actualRepairModelFirstDefect_supported_coefficient_contDiffOn
    {P Label : Type*} [TopologicalSpace P]
    (phase : Label → P → ℝ) (tau : ℝ) (R Q : Label → P → V)
    (W : Set P) (hW : IsOpen W) (K : Label → Set P)
    (hRsupport : ∀ l, tsupport (fun z : W => R l z) ⊆ Subtype.val ⁻¹' K l)
    (hQsupport : ∀ l, tsupport (fun z : W => Q l z) ⊆ Subtype.val ⁻¹' K l)
    (kappa : X → P) (Omega : Set X) (hOmega : IsOpen Omega)
    (hkappa : ContinuousOn kappa Omega) (hmap : MapsTo kappa Omega W)
    (O : Label → Set X) (hO : ∀ l, IsOpen (O l))
    (hcover : ∀ l, Omega ∩ kappa ⁻¹' K l ⊆ O l)
    (hphase : ∀ l, ContDiffOn ℝ ∞ (phase l ∘ kappa) (O l))
    (hR : ∀ l, ContDiffOn ℝ ∞ (R l ∘ kappa) Omega)
    (hQ : ∀ l, ContDiffOn ℝ ∞ (Q l ∘ kappa) Omega) :
    ∀ l, ContDiffOn ℝ ∞ (fun z => incrementsSecondaryPhysicalCoefficient
      (fun l b x => phase l (kappa (b,x))) tau (fun (_ : Label) (_ : Ep) (_ : Unit) _ => 1)
      (fun l b (_ : Unit) x => R l (kappa (b,x)))
      (fun l b (_ : Unit) x => Q l (kappa (b,x)))
      (fun i _ => EuclideanSpace.single i 1) z l) Omega := by
  intro l z hz
  by_cases ha : kappa z ∈ K l
  · have hlocal : ContDiffOn ℝ ∞ (fun w => incrementsSecondaryPhysicalCoefficient
        (fun l b x => phase l (kappa (b,x))) tau (fun (_ : Label) (_ : Ep) (_ : Unit) _ => 1)
        (fun l b (_ : Unit) x => R l (kappa (b,x)))
        (fun l b (_ : Unit) x => Q l (kappa (b,x)))
        (fun i _ => EuclideanSpace.single i 1) w l) (Omega ∩ O l) := by
      apply contDiffOn_pi.mpr
      intro i
      apply contDiffOn_pi.mpr
      intro co
      exact actualRepairModelFirstDefect_coefficient_contDiffOn
        (R l ∘ kappa) (Q l ∘ kappa) (phase l ∘ kappa) tau (EuclideanSpace.single i 1) co
        (Omega ∩ O l) (hOmega.inter (hO l)) ((hR l).mono inter_subset_left)
        ((hQ l).mono inter_subset_left) ((hphase l).mono inter_subset_right)
    exact (hlocal.contDiffAt ((hOmega.inter (hO l)).mem_nhds ⟨hz,hcover l ⟨hz,ha⟩⟩)).contDiffWithinAt
  · have hr := parameterRound2_relative_observation_zero_germ (R l) W (K l) hW (hRsupport l)
      kappa z (hkappa.continuousAt (hOmega.mem_nhds hz)) (hmap hz) ha
    have hq := parameterRound2_relative_observation_zero_germ (Q l) W (K l) hW (hQsupport l)
      kappa z (hkappa.continuousAt (hOmega.mem_nhds hz)) (hmap hz) ha
    have hc := round4_complete_observed_coefficient_zero_germ
      (R l ∘ kappa) (Q l ∘ kappa) (phase l ∘ kappa) tau
      (fun i : Fin (m+1) => EuclideanSpace.single i 1) z hr hq
    exact (contDiffAt_const.congr_of_eventuallyEq hc).contDiffWithinAt

/-- The same finite opposite mean is smooth; its regularity is an output. -/
theorem actualRepairModelFirstDefect_supported_mean_contDiffOn
    {P Label : Type*} [TopologicalSpace P] [Fintype Label] [DecidableEq Label]
    (phase : Label → P → ℝ) (tau : ℝ) (R Q : Label → P → V)
    (W : Set P) (hW : IsOpen W) (K : Label → Set P)
    (hRsupport : ∀ l, tsupport (fun z : W => R l z) ⊆ Subtype.val ⁻¹' K l)
    (hQsupport : ∀ l, tsupport (fun z : W => Q l z) ⊆ Subtype.val ⁻¹' K l)
    (kappa : X → P) (Omega : Set X) (hOmega : IsOpen Omega)
    (hkappa : ContinuousOn kappa Omega) (hmap : MapsTo kappa Omega W)
    (O : Label → Set X) (hO : ∀ l, IsOpen (O l))
    (hcover : ∀ l, Omega ∩ kappa ⁻¹' K l ⊆ O l)
    (hphase : ∀ l, ContDiffOn ℝ ∞ (phase l ∘ kappa) (O l))
    (hR : ∀ l, ContDiffOn ℝ ∞ (R l ∘ kappa) Omega)
    (hQ : ∀ l, ContDiffOn ℝ ∞ (Q l ∘ kappa) Omega) :
    ContDiffOn ℝ ∞ (actualPrimaryOppositeMeanTensor (fun l b x => phase l (kappa (b,x))) tau
      (fun (_ : Label) (_ : Ep) (_ : Unit) _ => 1)
      (fun l b (_ : Unit) x => R l (kappa (b,x)))
      (fun l b (_ : Unit) x => Q l (kappa (b,x)))) Omega := by
  exact actual_primary_opposite_mean_contDiffOn _ tau _ _ _ Omega
    (actualRepairModelFirstDefect_supported_coefficient_contDiffOn phase tau R Q W hW K hRsupport hQsupport
      kappa Omega hOmega hkappa hmap O hO hcover hphase hR hQ)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualRepairModelFirstDefect_supported_mean_contDiffOn
