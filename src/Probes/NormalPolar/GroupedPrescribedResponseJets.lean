import NormalPolar.GlobalWaveResponsePrescribedRawJets
import NormalPolar.JointSecondaryGroupedVariableWave

noncomputable section
open Set Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Continuation GlobalEmbedding.Upgrade
variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N p r : ℕ} {Sub : Fin r → Type*} [∀ l, Fintype (Sub l)]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

theorem groupedPrescribed_native_directional_jets
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : (l : Fin r) → Sub l → Ep → D → M) (chi : (l : Fin r) → Sub l → X → ℝ)
    (nu : (l : Fin r) → (s : Sub l) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l s b x))
    (a : (l : Fin r) → Sub l → OpenPartialHomeomorph (Ep × M) X) (W : Set (Ep × M)) (K : Fin r → Set (Ep × M))
    (pieceK : (l : Fin r) → Sub l → Set (Ep × M))
    (hW : IsOpen W) (hsub : ∀ l s, pieceK l s ⊆ K l) (n length j : ℕ) (horder : j+1+length ≤ n)
    (tau ell delta : ℝ) (weight : Fin r → ℝ) (Mg Bchi Bnu : ℝ)
    (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hMg : 0 ≤ Mg) (hdelta : 0 ≤ delta) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu)
    (kappa : Y → Ep × M) (Omega S : Set Y) (hOmega : IsOpen Omega) (hS : S ⊆ Omega)
    (hkappa : ContinuousOn kappa Omega) (hmap : MapsTo kappa Omega W)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (phase : Fin r → Ep × M → ℝ) (Mphase : ℝ)
    (profiles : JointGroupedPrescribedObservationProfiles F hF c chi nu a W pieceK n j ell Mg Bchi Bnu
      kappa Omega S T phase Mphase)
    (L R : ℕ) (hL : ∀ y ∈ S, (Finset.univ.filter (fun l => kappa y ∈ K l)).card ≤ L)
    (hR : ∀ l y, y ∈ S → (Finset.univ.filter (fun s => kappa y ∈ pieceK l s)).card ≤ R)
    (u direction : ProbeParameters r) :
    let vf := fun l s => actualProbeNormalAmplitude F (c l s) (chi l s) (nu l s) delta tau (weight l)
    let wave := fun v y => jointGroupedPrescribedWave label F hF c vf phase tau length a
      (probeParameterEmbedding label v) (kappa y)
    let response := fun y => fderiv ℝ (fun v => wave v y) u direction
    let C := globalWavePrescribedResponseCost m N n length j (L*R) T weight Mg Bchi Bnu Mphase
    response = wave direction ∧ ContDiffOn ℝ ∞ response Omega ∧
      ∀ k ≤ j, ∀ y ∈ S, tau^k*‖iteratedFDeriv ℝ k response y‖ ≤ C*delta*tau*‖direction‖ := by
  intro vf wave response C
  have hvf (l : Fin r) (s : Sub l) :
      ContDiffOn ℝ ∞ (fun z : X => (vf l s z.1 z.2 : V)) (a l s).target :=
    (((profiles.raw l s).cutoff_smooth.smul (profiles.raw l s).normal_smooth).const_smul
      (-(delta*tau)/(weight l)^2))
  have hresponse : response = wave direction := by
    funext y
    let L := probeColumnMap (fun q : Fin p => jointGroupedPrescribedWave label F hF c vf
      phase tau length a (Pi.single q 1) (kappa y))
    have he : (fun v : Fin p → ℝ =>
        jointGroupedPrescribedWave label F hF c vf phase tau length a v (kappa y)) = L := by
      funext v
      rw [show L v = ∑ q, v q • jointGroupedPrescribedWave label F hF c vf
        phase tau length a (Pi.single q 1) (kappa y) from probeColumnMap_apply _ _]
      exact jointGroupedPrescribedWave_columns label F hF c vf phase tau length a
        (fun l s => (profiles.raw l s).A_smooth) (fun l s => (profiles.raw l s).B_smooth)
        (fun l s => (profiles.raw l s).BR_smooth) hvf v (kappa y)
    change fderiv ℝ ((fun v => jointGroupedPrescribedWave label F hF c vf
      phase tau length a v (kappa y)) ∘ probeParameterEmbedding label) u direction = _
    rw [he]
    change (fderiv ℝ (L.comp (probeParameterEmbedding label).toContinuousLinearMap) u) direction = _
    rw [(L.comp (probeParameterEmbedding label).toContinuousLinearMap).hasFDerivAt.fderiv,
      ContinuousLinearMap.comp_apply]
    exact (congrFun he (probeParameterEmbedding label direction)).symm
  have hraw := jointGrouped_prescribed_wave_from_raw label F hF c chi nu a W K pieceK hW hsub
    n length j horder tau ell delta weight Mg Bchi Bnu ‖direction‖ htau htaul hell1
    hMg hdelta hBchi hBnu (norm_nonneg _)
    kappa Omega S hOmega hS hkappa hmap T hT phase Mphase profiles L R hL hR
    (probeParameterEmbedding label direction) (by rw [probeParameterEmbedding_norm])
  have hscale :
      actualFinitePrimaryJetConstant (L*R) N j Mphase
        (actualPrescribedRawAmplitudeCost m N n length j T weight Mg Bchi Bnu ‖direction‖ false)
        (actualPrescribedRawAmplitudeCost m N n length j T weight Mg Bchi Bnu ‖direction‖ true) =
      C*‖direction‖ := by
    simp only [C,globalWavePrescribedResponseCost,actualFinitePrimaryJetConstant,
      actualPrescribedRawAmplitudeCost,← Finset.sum_mul,mul_one]
    ring
  refine ⟨hresponse,?_,?_⟩
  · rw [hresponse]
    exact hraw.1
  · intro k hk y hy
    rw [hresponse]
    exact (hraw.2 k hk y hy).trans_eq (by rw [hscale]; ring)

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.groupedPrescribed_native_directional_jets
