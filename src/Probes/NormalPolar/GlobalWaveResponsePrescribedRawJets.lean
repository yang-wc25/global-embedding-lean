import NormalPolar.GlobalWaveResponseCharts
import NormalPolar.ParameterDisplacementPrescribedWave
import Probes.Round4OriginalProbeParameters

/-! Sharp native parameter-response jets of the SAME complete prescribed
wave are produced from its actual raw cutoff, normal, solver, chart and phase
profiles. Exact linearity in the original paired parameter identifies its
native derivative with the full wave at the actual direction. The cost is
fixed before the scales, fields, base parameter and direction. -/
noncomputable section
open Set Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Continuation GlobalEmbedding.Upgrade
variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N p r : ℕ}
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

def globalWavePrescribedResponseCost (m N n length j L : ℕ)
    (T : ℕ → ℝ) (weight : Fin r → ℝ) (Mg Bchi Bnu Mphase : ℝ) : ℝ :=
  actualFinitePrimaryJetConstant L N j Mphase
    (actualPrescribedRawAmplitudeCost m N n length j T weight Mg Bchi Bnu 1 false)
    (actualPrescribedRawAmplitudeCost m N n length j T weight Mg Bchi Bnu 1 true)

theorem globalWavePrescribedResponseCost_nonneg (m N n length j L : ℕ)
    (T : ℕ → ℝ) (weight : Fin r → ℝ) (Mg Bchi Bnu Mphase : ℝ)
    (hT : ∀ k, 0 ≤ T k) (hMg : 0 ≤ Mg) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu) :
    0 ≤ globalWavePrescribedResponseCost m N n length j L T weight Mg Bchi Bnu Mphase :=
  actualFinitePrimaryJetConstant_nonneg L N j Mphase
    (actualPrescribedRawAmplitudeCost_nonneg m N n length j T weight Mg Bchi Bnu 1 false
      hT hMg hBchi hBnu zero_le_one)
    (actualPrescribedRawAmplitudeCost_nonneg m N n length j T weight Mg Bchi Bnu 1 true
      hT hMg hBchi hBnu zero_le_one)

private theorem globalWavePrescribedResponseCost_scale (m N n length j L : ℕ)
    (T : ℕ → ℝ) (weight : Fin r → ℝ) (Mg Bchi Bnu Mphase rho : ℝ) :
    actualFinitePrimaryJetConstant L N j Mphase
      (actualPrescribedRawAmplitudeCost m N n length j T weight Mg Bchi Bnu rho false)
      (actualPrescribedRawAmplitudeCost m N n length j T weight Mg Bchi Bnu rho true) =
    globalWavePrescribedResponseCost m N n length j L T weight Mg Bchi Bnu Mphase * rho := by
  simp only [globalWavePrescribedResponseCost,actualFinitePrimaryJetConstant,
    actualPrescribedRawAmplitudeCost,← Finset.sum_mul,mul_one]
  ring

/-- Arbitrary original paired directions, with no finite-column summation
loss and no global phase extension. All spatial jets are actual derivatives
of the native parameter derivative, not a supplied response family. -/
theorem globalWave_prescribed_native_directional_jets
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M) (chi : Fin r → X → ℝ)
    (nu : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X) (W : Set (Ep × M)) (K : Fin r → Set (Ep × M))
    (hW : IsOpen W) (n length j : ℕ) (horder : j+1+length ≤ n)
    (tau ell delta : ℝ) (weight : Fin r → ℝ) (Mg Bchi Bnu : ℝ)
    (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hMg : 0 ≤ Mg) (hdelta : 0 ≤ delta) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu)
    (kappa : Y → Ep × M) (Omega S : Set Y) (hOmega : IsOpen Omega) (hS : S ⊆ Omega)
    (hkappa : ContinuousOn kappa Omega) (hmap : MapsTo kappa Omega W)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (phase : Fin r → Ep × M → ℝ) (Mphase : ℝ)
    (profiles : ActualPrescribedObservationProfiles F hF c chi nu a W K n j ell Mg Bchi Bnu
      kappa Omega S T phase Mphase)
    (L : ℕ) (hL : ∀ y ∈ S, (Finset.univ.filter (fun l => kappa y ∈ K l)).card ≤ L)
    (u direction : ProbeParameters r) :
    let vf := fun l => actualProbeNormalAmplitude F (c l) (chi l) (nu l) delta tau (weight l)
    let wave := fun v y => round4PrescribedGlobalWave label F hF c vf phase tau length a
      (probeParameterEmbedding label v) (kappa y)
    let response := fun y => fderiv ℝ (fun v => wave v y) u direction
    let C := globalWavePrescribedResponseCost m N n length j L T weight Mg Bchi Bnu Mphase
    response = wave direction ∧ ContDiffOn ℝ ∞ response Omega ∧
      ∀ k ≤ j, ∀ y ∈ S, tau^k*‖iteratedFDeriv ℝ k response y‖ ≤ C*delta*tau*‖direction‖ := by
  intro vf wave response C
  have hvf (l : Fin r) : ContDiffOn ℝ ∞ (fun z : X => (vf l z.1 z.2 : V)) (a l).target :=
    (((profiles.raw l).cutoff_smooth.smul (profiles.raw l).normal_smooth).const_smul
      (-(delta*tau)/(weight l)^2))
  have hresponse : response = wave direction := by
    funext y
    have hd := (round4PrescribedGlobalWave_hasFDerivAt label F hF c vf phase tau length a
      (fun l => (profiles.raw l).A_smooth) (fun l => (profiles.raw l).B_smooth)
      (fun l => (profiles.raw l).BR_smooth) hvf (probeParameterEmbedding label u) (kappa y)).comp u
      (probeParameterEmbedding label).toContinuousLinearMap.hasFDerivAt
    change fderiv ℝ ((fun v => round4PrescribedGlobalWave label F hF c vf phase tau length a v
      (kappa y)) ∘ probeParameterEmbedding label) u direction = _
    rw [hd.fderiv,ContinuousLinearMap.comp_apply]
    change probeColumnMap _ (probeParameterEmbedding label direction) = _
    rw [probeColumnMap_apply]
    exact (round4PrescribedGlobalWave_columns label F hF c vf phase tau length a
      (fun l => (profiles.raw l).A_smooth) (fun l => (profiles.raw l).B_smooth)
      (fun l => (profiles.raw l).BR_smooth) hvf (probeParameterEmbedding label direction) (kappa y)).symm
  have hraw := actual_prescribed_wave_from_raw label F hF c chi nu a W K hW n length j horder
    tau ell delta weight Mg Bchi Bnu ‖direction‖ htau htaul hell1 hMg hdelta hBchi hBnu (norm_nonneg _)
    kappa Omega S hOmega hS hkappa hmap T hT phase Mphase profiles L hL
    (probeParameterEmbedding label direction) (by rw [probeParameterEmbedding_norm])
  refine ⟨hresponse,?_,?_⟩
  · rw [hresponse]
    exact hraw.1
  · intro k hk y hy
    rw [hresponse]
    have hh := hraw.2 k hk y hy
    rw [globalWavePrescribedResponseCost_scale] at hh
    exact hh.trans_eq (by ring)

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.globalWave_prescribed_native_directional_jets
