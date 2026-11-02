import NormalPolar.ParameterDisplacementPrescribedPhysicalObserved
import NormalPolar.ParameterDisplacementPrescribedPhysicalGlobal
import NormalPolar.JointSecondaryGroupedWave
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

variable {m N p r : ℕ} {Sub : Fin r → Type*} [∀ l, Fintype (Sub l)] {Ep Eq M : Type*}
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

theorem jointGrouped_prescribed_global_physical_from_raw
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (c : (l : Fin r) → Sub l → Ep → D → M) (chi : (l : Fin r) → Sub l → X → ℝ)
    (nu : (l : Fin r) → (s : Sub l) → (b : Ep) → (x : D) → normalSpace (I := IM) (F b) (c l s b x))
    (a : (l : Fin r) → Sub l → OpenPartialHomeomorph (Ep × M) X) (W : Set (Ep × M)) (K : Fin r → Set (Ep × M))
    (pieceK : (l : Fin r) → Sub l → Set (Ep × M))
    (hW : IsOpen W) (hsub : ∀ l s, pieceK l s ⊆ K l) (n length j : ℕ) (horder : j+length ≤ n)
    (tau ell delta : ℝ) (weight : Fin r → ℝ) (Mg Bchi Bnu rho : ℝ)
    (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hdelta : 0 ≤ delta) (hweight : ∀ l, weight l ≠ 0)
    (hMg : 0 ≤ Mg) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu) (hrho : 0 ≤ rho)
    (kappa : Y → Ep × M) (parameter : Eq → Ep) (hfirst : ∀ z, (kappa z).1 = parameter z.1)
    (Omega S : Set Y) (hOmega : IsOpen Omega) (hS : S ⊆ Omega)
    (hkappa : ContinuousOn kappa Omega) (hmap : MapsTo kappa Omega W)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (phase : Fin r → Ep × M → ℝ) (Mphase : ℝ)
    (profiles : JointGroupedPrescribedObservationProfiles F hF c chi nu a W pieceK n (j+1) ell Mg Bchi Bnu
      kappa Omega S T phase Mphase)
    (geom : ∀ l s, ActualPrescribedPhysicalGeometry F hF (c l s) (nu l s) (a l s) (phase l))
    (L R : ℕ) (hL : ∀ y ∈ S, (Finset.univ.filter (fun l => kappa y ∈ K l)).card ≤ L)
    (hR : ∀ l y, y ∈ S → (Finset.univ.filter (fun s => kappa y ∈ pieceK l s)).card ≤ R)
    (u : Fin p → ℝ) (hu : ‖u‖ ≤ rho) :
    let vf := fun l s => actualProbeNormalAmplitude F (c l s) (chi l s) (nu l s) delta tau (weight l)
    let Fobs := fun z : Y => F (kappa z).1 (kappa z).2
    let wave := jointGroupedPrescribedWave label F hF c vf phase tau length a u ∘ kappa
    let E := actualJointMetricLinearization Fobs wave
    let C := ((L*R : ℕ) : ℝ)*actualPrescribedRawPhysicalCost m N n length j T weight Mg Bchi Bnu*rho
    ContDiffOn ℝ ∞ wave Omega ∧ ContDiffOn ℝ ∞ E Omega ∧
      ∀ k ≤ j, ∀ y ∈ S, tau^k*‖iteratedFDeriv ℝ k E y‖ ≤ C*delta*tau*(tau/ell)^length := by
  intro vf Fobs wave E C
  let piece := fun (l : Fin r) (s : Sub l) => actualPrescribedPhysicalPiece label l F hF (c l s) (vf l s) (phase l) tau length (a l s) u
  let Cbase := actualPrescribedRawPhysicalCost m N n length j T weight Mg Bchi Bnu
  let Budget := Cbase*(tau/ell)^length*(delta*tau)*rho
  have hCbase : 0 ≤ Cbase := actualPrescribedRawPhysicalCost_nonneg _ _ _ _ _ _ _ _ _ _ hT hMg hBchi hBnu
  have hell : 0 < ell := htau.trans_le htaul
  have hBudget : 0 ≤ Budget := by dsimp only [Budget]; positivity
  have hp (l : Fin r) (s : Sub l) := actual_prescribed_raw_observed_physical label l F hF (c l s) (chi l s) (nu l s)
    (a l s) W (pieceK l s) hW (phase l) n length j horder tau ell delta (weight l) Mg Bchi Bnu
    htau htaul hell1 hdelta (hweight l) hMg hBchi hBnu (profiles.raw l s) (geom l s)
    kappa parameter (profiles.domains l s) (S ∩ kappa ⁻¹' pieceK l s) (profiles.domains_open l s)
    (fun y hy => profiles.active_domain l s ⟨hS hy.1,hy.2⟩) (profiles.source l s) (fun z _ => hfirst z)
    (profiles.transition_smooth l s) (profiles.sample l s) T hT
    (fun z hz k hk hkj => profiles.transition_jets l s k hk hkj z hz) u
  have hbound (l : Fin r) (s : Sub l) (k : ℕ) (hk : k ≤ j) (y : Y) (hy : y ∈ S ∩ kappa ⁻¹' pieceK l s) :
      tau^k*‖iteratedFDeriv ℝ k (actualJointMetricLinearization Fobs (piece l s ∘ kappa)) y‖ ≤ Budget := by
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
      _ ≤ Cl*(tau/ell)^length*(delta*tau)*‖u‖ := (hp l s).2.2.2 k hk y hy
      _ ≤ Cl*(tau/ell)^length*(delta*tau)*rho := mul_le_mul_of_nonneg_left hu (by positivity)
      _ ≤ Cbase*(tau/ell)^length*(delta*tau)*rho := by gcongr
      _ = Budget := rfl
  have hcount (y : Y) (hy : y ∈ S) :
      (Finset.univ.filter (fun t : Sigma Sub => kappa y ∈ pieceK t.1 t.2)).card ≤ L*R :=
    jointGrouped_active_piece_count K pieceK hsub (kappa y) L R (hL y hy) (fun l => hR l y hy)
  have hsum := actual_primary_physical_sum_weighted_jets Fobs
    (fun (t : Sigma Sub) (_ : Unit) => piece t.1 t.2)
    (fun t => pieceK t.1 t.2) (fun t (_ : Unit) => pieceK t.1 t.2)
    (fun _ _ => Subset.rfl) W hW (fun t _ => (hp t.1 t.2).1)
    kappa Omega S hOmega hS hkappa hmap (fun t (_ : Unit) => profiles.domains t.1 t.2)
    (fun t _ => profiles.domains_open t.1 t.2) (fun t _ => profiles.active_domain t.1 t.2)
    (fun t _ => (hp t.1 t.2).2.1) (fun t _ => (hp t.1 t.2).2.2.1) (L*R) 1 j hcount
    (fun _ _ _ => (Finset.card_le_univ _).trans_eq (by simp))
    tau Budget htau hBudget (fun t _ k hk y hy => hbound t.1 t.2 k hk y hy)
  have hactual : wave = fun z => ∑ t : Sigma Sub, ∑ _q : Unit, piece t.1 t.2 (kappa z) := by
    funext z
    simp only [Finset.univ_unique,Finset.sum_singleton,Fintype.sum_sigma]
    exact jointGroupedPrescribedWave_eq_piece_sum label F hF c vf phase tau length a u (kappa z)
  rw [← hactual] at hsum
  refine ⟨hsum.1,hsum.2.1,?_⟩
  intro k hk y hy
  have hb := hsum.2.2 (1 : ℝ) k hk y hy
  simpa only [one_smul,abs_one,mul_one,Nat.mul_one] using
    hb.trans_eq (by dsimp only [C,Budget,Cbase]; simp only [Nat.mul_one]; ring)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.jointGrouped_prescribed_global_physical_from_raw
