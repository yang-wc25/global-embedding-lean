import NormalPolar.ActualRepairModelFirstDefectCommonRegular
import NormalPolar.ActualRepairModelFirstDefectPhaseJet
import Probes.Round4PrescribedObservedCoefficientJets
import Smoothing.ParameterRound2MeanPrimitives

/-! Complete prescribed physical coefficients, including all original spatial
and auxiliary derivatives, are produced from the actual normal source. The
slow bound is fixed by primitive constants, before maps, scales and u. Relative
support removes all phase requirements on inactive modes. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {E H M Ep Eq : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Eq] [NormedSpace ℝ Eq] {m N p r : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Y" => Eq × D

def actualRepairModelFirstDefectPrescribedCoefficientCost
    (m N n length j : ℕ) (T : ℕ → ℝ) (weight Mg Bchi Bnu Mphase rho : ℝ) : ℝ :=
  let CR := round4ObservationJetCost T (j+1)*round4PrescribedAmplitudeJetCost m N n length (j+1) false weight Mg Bchi Bnu
  let CQ := round4ObservationJetCost T (j+1)*round4PrescribedAmplitudeJetCost m N n length (j+1) true weight Mg Bchi Bnu
  (∑ s : Fin (m+1) × Fin N, round4CompleteCoefficientJetCost j (EuclideanSpace.single s.1 1) s.2 CR CQ
    (‖ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single s.1 1 : EuclideanSpace ℝ (Fin (m+1)))‖*Mphase))*rho

theorem actualRepairModelFirstDefect_prescribed_coefficient_cost_nonneg
    (m N n length j : ℕ) (T : ℕ → ℝ) (weight Mg Bchi Bnu Mphase rho : ℝ)
    (hT : ∀ k, 0 ≤ T k) (hMg : 0 ≤ Mg) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu)
    (hMphase : 0 ≤ Mphase) (hrho : 0 ≤ rho) :
    0 ≤ actualRepairModelFirstDefectPrescribedCoefficientCost m N n length j T weight Mg Bchi Bnu Mphase rho := by
  have hR := round4PrescribedAmplitudeJetCost_nonneg m N n length (j+1) false weight hMg hBchi hBnu
  have hQ := round4PrescribedAmplitudeJetCost_nonneg m N n length (j+1) true weight hMg hBchi hBnu
  have hTC := round4ObservationJetCost_nonneg T hT (j+1)
  unfold actualRepairModelFirstDefectPrescribedCoefficientCost round4CompleteCoefficientJetCost
  apply mul_nonneg _ hrho
  apply Finset.sum_nonneg
  intro s _
  positivity

theorem actualRepairModelFirstDefect_prescribed_coefficients_from_raw
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M) (chi : Fin r → X → ℝ)
    (nu : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X) (W : Set (Ep × M)) (K : Fin r → Set (Ep × M))
    (hW : IsOpen W) (n length j : ℕ) (horder : j+2+length ≤ n)
    (tau ell delta : ℝ) (weight : Fin r → ℝ) (Mg Bchi Bnu rho Mphase : ℝ)
    (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hMg : 0 ≤ Mg) (hdelta : 0 ≤ delta) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu)
    (hrho : 0 ≤ rho) (hMphase : 0 ≤ Mphase)
    (kappa : Y → Ep × M) (Omega S : Set Y) (hOmega : IsOpen Omega) (hS : S ⊆ Omega)
    (hkappa : ContMDiffOn 𝓘(ℝ,Y) ((𝓘(ℝ,Ep)).prod I) ∞ kappa Omega)
    (hmap : MapsTo kappa Omega W) (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (phase : Fin r → Ep × M → ℝ)
    (profiles : ActualPrescribedObservationProfiles F hF c chi nu a W K n (j+1) ell Mg Bchi Bnu
      kappa Omega S T phase Mphase)
    (u : Fin p → ℝ) (hu : ‖u‖ ≤ rho) :
    let vf := fun l => actualProbeNormalAmplitude F (c l) (chi l) (nu l) delta tau (weight l)
    let R := fun l => round4PrescribedGlobalAmplitude false label l F hF (c l) (vf l) tau length (a l) u
    let Q := fun l => round4PrescribedGlobalAmplitude true label l F hF (c l) (vf l) tau length (a l) u
    let coeff := fun l z => incrementsSecondaryPhysicalCoefficient (fun l b x => phase l (kappa (b,x))) tau
      (fun (_ : Fin r) (_ : Eq) (_ : Unit) _ => 1)
      (fun l b (_ : Unit) x => R l (kappa (b,x))) (fun l b (_ : Unit) x => Q l (kappa (b,x)))
      (fun i _ => EuclideanSpace.single i 1) z l
    ∀ l, ContDiffOn ℝ ∞ (coeff l) Omega ∧
      (∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k (coeff l) z‖ ≤
        actualRepairModelFirstDefectPrescribedCoefficientCost m N n length j T (weight l) Mg Bchi Bnu Mphase rho*delta) ∧
      (∀ z ∈ Omega, kappa z ∉ K l → coeff l =ᶠ[𝓝 z] 0) := by
  intro vf R Q coeff
  have hell : 0 < ell := htau.trans_le htaul
  have hamp (ch : Bool) (l : Fin r) := actualRepairModelFirstDefect_prescribed_amplitude_regular ch label l
    F hF (c l) (chi l) (nu l) (a l) W (K l) hW n (j+1) length ell Mg Bchi Bnu tau delta
    (weight l) (profiles.raw l) u
  have hR : ∀ l, ContDiffOn ℝ ∞ (R l ∘ kappa) Omega :=
    fun l => ((hamp false l).1.comp hkappa hmap).contDiffOn
  have hQ : ∀ l, ContDiffOn ℝ ∞ (Q l ∘ kappa) Omega :=
    fun l => ((hamp true l).1.comp hkappa hmap).contDiffOn
  have hcoef := actualRepairModelFirstDefect_supported_coefficient_contDiffOn phase tau R Q W hW K
    (fun l => (hamp false l).2) (fun l => (hamp true l).2) kappa Omega hOmega hkappa.continuousOn hmap
    profiles.domains profiles.domains_open profiles.active_domain profiles.phase_smooth hR hQ
  have hzero (l : Fin r) (z : Y) (hz : z ∈ Omega) (hn : kappa z ∉ K l) : coeff l =ᶠ[𝓝 z] 0 := by
    have hr := parameterRound2_relative_observation_zero_germ (R l) W (K l) hW (hamp false l).2
      kappa z (hkappa.continuousOn.continuousAt (hOmega.mem_nhds hz)) (hmap hz) hn
    have hq := parameterRound2_relative_observation_zero_germ (Q l) W (K l) hW (hamp true l).2
      kappa z (hkappa.continuousOn.continuousAt (hOmega.mem_nhds hz)) (hmap hz) hn
    exact round4_complete_observed_coefficient_zero_germ (R l ∘ kappa) (Q l ∘ kappa)
      (phase l ∘ kappa) tau (fun i : Fin (m+1) => EuclideanSpace.single i 1) z hr hq
  intro l
  let raw := profiles.raw l
  let O := profiles.domains l
  let S0 := S ∩ kappa ⁻¹' K l
  have hS0 : S0 ⊆ O := fun z hz => profiles.active_domain l ⟨hS hz.1,hz.2⟩
  let CR := round4ObservationJetCost T (j+1)*round4PrescribedAmplitudeJetCost m N n length (j+1) false (weight l) Mg Bchi Bnu
  let CQ := round4ObservationJetCost T (j+1)*round4PrescribedAmplitudeJetCost m N n length (j+1) true (weight l) Mg Bchi Bnu
  let cost := fun s : Fin (m+1) × Fin N => round4CompleteCoefficientJetCost j (EuclideanSpace.single s.1 1) s.2 CR CQ
    (‖ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single s.1 1 : D)‖*Mphase)
  let Csum := ∑ s, cost s
  have hCR : 0 ≤ CR := mul_nonneg (round4ObservationJetCost_nonneg T hT (j+1))
    (round4PrescribedAmplitudeJetCost_nonneg m N n length (j+1) false (weight l) hMg hBchi hBnu)
  have hCQ : 0 ≤ CQ := mul_nonneg (round4ObservationJetCost_nonneg T hT (j+1))
    (round4PrescribedAmplitudeJetCost_nonneg m N n length (j+1) true (weight l) hMg hBchi hBnu)
  have hcost (s : Fin (m+1) × Fin N) : 0 ≤ cost s := by
    dsimp only [cost,round4CompleteCoefficientJetCost]
    positivity
  have hCsum : 0 ≤ Csum := Finset.sum_nonneg (fun s _ => hcost s)
  have hcostsum (s : Fin (m+1) × Fin N) : cost s ≤ Csum :=
    Finset.single_le_sum (fun t _ => hcost t) (Finset.mem_univ s)
  have hgrad (i : Fin (m+1)) := (actualRepairModelFirstDefect_phase_directional_jets
    (phase l ∘ kappa) (EuclideanSpace.single i 1) O S0 (profiles.domains_open l) hS0
    (profiles.phase_smooth l) j ell Mphase hell.le
    (fun k hk z hz => profiles.phase_jets l k (by omega) z hz)).2
  have hc (i : Fin (m+1)) (co : Fin N) := round4_prescribed_observed_coefficient_all_weighted_jets
    label l F hF (c l) (chi l) (nu l) n length j horder (a l).target raw.sample (a l).open_target
    raw.sample_subset raw.A_smooth raw.B_smooth raw.G_smooth raw.J_smooth raw.T_smooth raw.BR_smooth
    raw.cutoff_smooth raw.normal_smooth tau ell delta (weight l) Mg Bchi Bnu htau htaul hell1
    hMg hdelta hBchi hBnu raw.A_jets raw.B_jets raw.G_jets raw.J_jets raw.T_jets raw.BR_jets
    raw.cutoff_jets raw.normal_jets (a l) Subset.rfl kappa O S0 (profiles.domains_open l) hS0
    (profiles.source l) (profiles.transition_smooth l) (profiles.sample l) T hT
    (profiles.transition_jets l) (phase l) (EuclideanSpace.single i 1) co
    (‖ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1 : D)‖*Mphase)
    (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) hMphase) (profiles.phase_smooth l) (hgrad i) u
  have hBudget : 0 ≤ actualRepairModelFirstDefectPrescribedCoefficientCost
      m N n length j T (weight l) Mg Bchi Bnu Mphase rho*delta := mul_nonneg
    (actualRepairModelFirstDefect_prescribed_coefficient_cost_nonneg m N n length j T (weight l)
      Mg Bchi Bnu Mphase rho hT hMg hBchi hBnu hMphase hrho) hdelta
  refine ⟨hcoef l,?_,hzero l⟩
  intro k hk z hz
  by_cases ha : kappa z ∈ K l
  · have hsm := (hcoef l).contDiffAt (hOmega.mem_nhds (hS hz))
    apply parameterRound2_joint_pi_weighted_jet (coeff l) z hsm k ell _ hell hBudget
    intro i
    apply parameterRound2_joint_pi_weighted_jet _ z (contDiffAt_pi.1 hsm i) k ell _ hell hBudget
    intro co
    calc
      _ ≤ cost (i,co)*delta*‖u‖ := (hc i co).2 k hk z ⟨hz,ha⟩
      _ ≤ Csum*delta*rho := by gcongr; exact hcostsum _
      _ = _ := by unfold actualRepairModelFirstDefectPrescribedCoefficientCost; dsimp only [Csum,cost,CR,CQ]; ring
  · rw [((hzero l z (hS hz) ha).iteratedFDeriv ℝ k).eq_of_nhds]
    simpa using mul_nonneg
      (actualRepairModelFirstDefect_prescribed_coefficient_cost_nonneg m N n length j T (weight l)
        Mg Bchi Bnu Mphase rho hT hMg hBchi hBnu hMphase hrho) hdelta

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualRepairModelFirstDefect_prescribed_coefficients_from_raw
