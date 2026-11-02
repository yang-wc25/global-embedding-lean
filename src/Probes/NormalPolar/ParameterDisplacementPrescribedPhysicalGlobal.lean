import NormalPolar.ParameterDisplacementPrescribedPhysicalObserved
import NormalPolar.ParameterDisplacementPrescribedWave
import Probes.ActualIncrementPrimaryPhysicalSum

/-!
# Full prescribed physical residual from raw geometry and actual support

The same complete global prescribed wave is used throughout. Its linearized
metric is summed only after true local identities and zero germs have been
proved, retaining the actual overlap count and finite accuracy gain.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold Filter GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m N p r : ℕ} {Ep Eq M : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Eq] [NormedSpace ℝ Eq]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Y" => Eq × D
local notation "IM" => 𝓘(ℝ,D)

private local instance prescribedGlobalTensorSemi : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance prescribedGlobalTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance prescribedGlobalTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

def actualPrescribedRawPhysicalCost (m N n length j : ℕ) (T : ℕ → ℝ)
    (weight : Fin r → ℝ) (Mg Bchi Bnu : ℝ) : ℝ :=
  ∑ l, actualFastTensorChartTransferPrefix T j *
    actualPrimaryPhysicalCost m N n length j Mg
      (probeNormalAmplitudeConstant n (weight l) Bchi Bnu)
      (probeNormalAmplitudeConstant n (weight l) Bchi Bnu)

theorem actualPrescribedRawPhysicalCost_nonneg (m N n length j : ℕ) (T : ℕ → ℝ)
    (weight : Fin r → ℝ) (Mg Bchi Bnu : ℝ)
    (hT : ∀ k, 0 ≤ T k) (hMg : 0 ≤ Mg) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu) :
    0 ≤ actualPrescribedRawPhysicalCost m N n length j T weight Mg Bchi Bnu := by
  apply Finset.sum_nonneg
  intro l _
  have hK := probeNormalAmplitudeConstant_nonneg n (weight l) hBchi hBnu
  exact mul_nonneg (actualFastTensorChartTransferPrefix_nonneg T hT j)
    (actualPrimaryPhysicalCost_nonneg m N n length j hMg hK hK)

theorem actual_prescribed_global_physical_from_raw
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M) (chi : Fin r → X → ℝ)
    (nu : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := IM) (F b) (c l b x))
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X) (W : Set (Ep × M)) (K : Fin r → Set (Ep × M))
    (hW : IsOpen W) (n length j : ℕ) (horder : j+length ≤ n)
    (tau ell delta : ℝ) (weight : Fin r → ℝ) (Mg Bchi Bnu rho : ℝ)
    (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hdelta : 0 ≤ delta) (hweight : ∀ l, weight l ≠ 0)
    (hMg : 0 ≤ Mg) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu) (hrho : 0 ≤ rho)
    (kappa : Y → Ep × M) (parameter : Eq → Ep) (hfirst : ∀ z, (kappa z).1 = parameter z.1)
    (Omega S : Set Y) (hOmega : IsOpen Omega) (hS : S ⊆ Omega)
    (hkappa : ContinuousOn kappa Omega) (hmap : MapsTo kappa Omega W)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (phase : Fin r → Ep × M → ℝ) (Mphase : ℝ)
    (profiles : ActualPrescribedObservationProfiles F hF c chi nu a W K n (j+1) ell Mg Bchi Bnu
      kappa Omega S T phase Mphase)
    (geom : ∀ l, ActualPrescribedPhysicalGeometry F hF (c l) (nu l) (a l) (phase l))
    (L : ℕ) (hL : ∀ y ∈ S, (Finset.univ.filter (fun l => kappa y ∈ K l)).card ≤ L)
    (u : Fin p → ℝ) (hu : ‖u‖ ≤ rho) :
    let vf := fun l => actualProbeNormalAmplitude F (c l) (chi l) (nu l) delta tau (weight l)
    let Fobs := fun z : Y => F (kappa z).1 (kappa z).2
    let wave := round4PrescribedGlobalWave label F hF c vf phase tau length a u ∘ kappa
    let E := actualJointMetricLinearization Fobs wave
    let C := (L : ℝ)*actualPrescribedRawPhysicalCost m N n length j T weight Mg Bchi Bnu*rho
    ContDiffOn ℝ ∞ wave Omega ∧ ContDiffOn ℝ ∞ E Omega ∧
      ∀ k ≤ j, ∀ y ∈ S, tau^k*‖iteratedFDeriv ℝ k E y‖ ≤ C*delta*tau*(tau/ell)^length := by
  intro vf Fobs wave E C
  let piece := fun l => actualPrescribedPhysicalPiece label l F hF (c l) (vf l) (phase l) tau length (a l) u
  let Cbase := actualPrescribedRawPhysicalCost m N n length j T weight Mg Bchi Bnu
  let Budget := Cbase*(tau/ell)^length*(delta*tau)*rho
  have hCbase : 0 ≤ Cbase := actualPrescribedRawPhysicalCost_nonneg _ _ _ _ _ _ _ _ _ _ hT hMg hBchi hBnu
  have hell : 0 < ell := htau.trans_le htaul
  have hBudget : 0 ≤ Budget := by dsimp only [Budget]; positivity
  have hp (l : Fin r) := actual_prescribed_raw_observed_physical label l F hF (c l) (chi l) (nu l)
    (a l) W (K l) hW (phase l) n length j horder tau ell delta (weight l) Mg Bchi Bnu
    htau htaul hell1 hdelta (hweight l) hMg hBchi hBnu (profiles.raw l) (geom l)
    kappa parameter (profiles.domains l) (S ∩ kappa ⁻¹' K l) (profiles.domains_open l)
    (fun y hy => profiles.active_domain l ⟨hS hy.1,hy.2⟩) (profiles.source l) (fun z _ => hfirst z)
    (profiles.transition_smooth l) (profiles.sample l) T hT
    (fun z hz k hk hkj => profiles.transition_jets l k hk hkj z hz) u
  have hbound (l : Fin r) (k : ℕ) (hk : k ≤ j) (y : Y) (hy : y ∈ S ∩ kappa ⁻¹' K l) :
      tau^k*‖iteratedFDeriv ℝ k (actualJointMetricLinearization Fobs (piece l ∘ kappa)) y‖ ≤ Budget := by
    let Cl := actualFastTensorChartTransferPrefix T j * actualPrimaryPhysicalCost m N n length j Mg
      (probeNormalAmplitudeConstant n (weight l) Bchi Bnu) (probeNormalAmplitudeConstant n (weight l) Bchi Bnu)
    have hCl : 0 ≤ Cl := by
      have hK := probeNormalAmplitudeConstant_nonneg n (weight l) hBchi hBnu
      exact mul_nonneg (actualFastTensorChartTransferPrefix_nonneg T hT j)
        (actualPrimaryPhysicalCost_nonneg m N n length j hMg hK hK)
    have hsum : Cl ≤ Cbase := by
      dsimp only [Cl,Cbase,actualPrescribedRawPhysicalCost]
      apply Finset.single_le_sum (f := fun q : Fin r => actualFastTensorChartTransferPrefix T j *
        actualPrimaryPhysicalCost m N n length j Mg (probeNormalAmplitudeConstant n (weight q) Bchi Bnu)
          (probeNormalAmplitudeConstant n (weight q) Bchi Bnu)) (fun q _ => ?_) (Finset.mem_univ l)
      have hK := probeNormalAmplitudeConstant_nonneg n (weight q) hBchi hBnu
      exact mul_nonneg (actualFastTensorChartTransferPrefix_nonneg T hT j)
        (actualPrimaryPhysicalCost_nonneg m N n length j hMg hK hK)
    calc
      _ ≤ Cl*(tau/ell)^length*(delta*tau)*‖u‖ := (hp l).2.2.2 k hk y hy
      _ ≤ Cl*(tau/ell)^length*(delta*tau)*rho := mul_le_mul_of_nonneg_left hu (by positivity)
      _ ≤ Cbase*(tau/ell)^length*(delta*tau)*rho := by gcongr
      _ = Budget := rfl
  have hsum := actual_primary_physical_sum_weighted_jets Fobs (fun l (_ : Unit) => piece l)
    K (fun l (_ : Unit) => K l) (fun _ _ => Subset.rfl) W hW (fun l _ => (hp l).1)
    kappa Omega S hOmega hS hkappa hmap (fun l (_ : Unit) => profiles.domains l)
    (fun l _ => profiles.domains_open l) (fun l _ => profiles.active_domain l)
    (fun l _ => (hp l).2.1) (fun l _ => (hp l).2.2.1) L 1 j hL
    (fun _ _ _ => (Finset.card_le_univ _).trans_eq (by simp))
    tau Budget htau hBudget (fun l _ k hk y hy => hbound l k hk y hy)
  have hactual : wave = fun z => ∑ l, ∑ _q : Unit, piece l (kappa z) := by
    simp only [wave,round4PrescribedGlobalWave,Function.comp_def,Finset.univ_unique,Finset.sum_singleton,piece,
      actualPrescribedPhysicalPiece]
  rw [← hactual] at hsum
  refine ⟨hsum.1,hsum.2.1,?_⟩
  intro k hk y hy
  have hb := hsum.2.2 (1 : ℝ) k hk y hy
  simpa only [one_smul,abs_one,mul_one,Nat.mul_one] using
    hb.trans_eq (by dsimp only [C,Budget,Cbase]; simp only [Nat.mul_one]; ring)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_prescribed_global_physical_from_raw
