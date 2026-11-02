import NormalPolar.ParameterDisplacementPrimarySupport
import Probes.Round4PrescribedAmplitudeObservation
import Probes.Round4PrescribedGlobalSmooth

/-!
# The prescribed spatial amplitudes from primitive normal-source geometry

The fields below precede the original finite mode reconstruction. They contain
only its actual cutoff, normal section, geometric coefficients and chart
transition. The complete two amplitudes, their relative support, and their
observed jets are conclusions, not supplied budgets.
-/

noncomputable section
open Set Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N p r : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

/-- The actual normal-source profiles on one genuine adapted chart. -/
structure ActualPrescribedSpatialRawProfiles
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Ep → D → M) (chi : X → ℝ)
    (nu : (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c b x))
    (a : OpenPartialHomeomorph (Ep × M) X) (W K : Set (Ep × M))
    (n j : ℕ) (ell Mg Bchi Bnu : ℝ) where
  sample : Set X
  sample_subset : sample ⊆ a.target
  closed_support : IsClosed (Subtype.val ⁻¹' K : Set W)
  support_source : K ⊆ a.source
  chart_smooth : ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,X) ∞ a a.source
  cutoff_support : ∀ z ∈ a.target, z ∈ tsupport chi → a.symm z ∈ K
  A_smooth : ContDiffOn ℝ ∞ (fun z : X =>
    incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c z.1) z.2) a.target
  B_smooth : ContDiffOn ℝ ∞ (fun z : X =>
    incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c z.1) z.2) a.target
  G_smooth : ContDiffOn ℝ ∞ (fun z : X =>
    freeGramRightInverse (fderiv ℝ (F z.1 ∘ c z.1) z.2)) a.target
  J_smooth : ContDiffOn ℝ ∞ (fun z : X =>
    (normalSpace (I := I) (F z.1) (c z.1 z.2)).subtypeL.comp
      (incrementsModeCoordinateJ (F z.1) (hF z.1) (c z.1) z.2)) a.target
  T_smooth : ContDiffOn ℝ ∞ (fun z : X =>
    incrementsModeTransverseValue (F z.1) (c z.1) z.2) a.target
  BR_smooth : ContDiffOn ℝ ∞ (fun z : X => fun k : Fin (m+1) =>
    (incrementsModeSecondForm (F z.1) (hF z.1) (c z.1) z.2 0 k : V)) a.target
  cutoff_smooth : ContDiffOn ℝ ∞ chi a.target
  normal_smooth : ContDiffOn ℝ ∞ (fun z : X => (nu z.1 z.2 : V)) a.target
  A_jets : ∀ k ≤ n, ∀ z ∈ sample, ell^k * ‖iteratedFDeriv ℝ k
    (fun w : X => incrementsModeComplexFirstOrderA (F w.1) (hF w.1) (c w.1) w.2) z‖ ≤ Mg
  B_jets : ∀ k ≤ n, ∀ z ∈ sample, ell^k * ‖iteratedFDeriv ℝ k
    (fun w : X => incrementsModeComplexFirstOrderB (F w.1) (hF w.1) (c w.1) w.2) z‖ ≤ Mg
  G_jets : ∀ k ≤ j, ∀ z ∈ sample, ell^k * ‖iteratedFDeriv ℝ k
    (fun w : X => freeGramRightInverse (fderiv ℝ (F w.1 ∘ c w.1) w.2)) z‖ ≤ Mg
  J_jets : ∀ k ≤ j, ∀ z ∈ sample, ell^k * ‖iteratedFDeriv ℝ k
    (fun w : X => (normalSpace (I := I) (F w.1) (c w.1 w.2)).subtypeL.comp
      (incrementsModeCoordinateJ (F w.1) (hF w.1) (c w.1) w.2)) z‖ ≤ Mg
  T_jets : ∀ k ≤ j, ∀ z ∈ sample, ell^k * ‖iteratedFDeriv ℝ k
    (fun w : X => incrementsModeTransverseValue (F w.1) (c w.1) w.2) z‖ ≤ Mg
  BR_jets : ∀ k ≤ n, ∀ z ∈ a.target, ell^k * ‖iteratedFDeriv ℝ k
    (fun w : X => fun q : Fin (m+1) =>
      (incrementsModeSecondForm (F w.1) (hF w.1) (c w.1) w.2 0 q : V)) z‖ ≤ Mg
  cutoff_jets : ∀ k ≤ n, ∀ z ∈ a.target, ell^k * ‖iteratedFDeriv ℝ k chi z‖ ≤ Bchi
  normal_jets : ∀ k ≤ n, ∀ z ∈ a.target, ell^k *
    ‖iteratedFDeriv ℝ k (fun w : X => (nu w.1 w.2 : V)) z‖ ≤ Bnu

/-- The actual finite solver produces both the global relative support and
all observed slow amplitude jets from the same primitive normal source. -/
theorem actual_prescribed_amplitude_from_raw
    (imag : Bool) (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Ep → D → M) (chi : X → ℝ)
    (nu : (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c b x))
    (a : OpenPartialHomeomorph (Ep × M) X) (W K : Set (Ep × M)) (hW : IsOpen W)
    (n length j : ℕ) (horder : j+1+length ≤ n)
    (tau ell delta lam Mg Bchi Bnu : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hMg : 0 ≤ Mg) (hdelta : 0 ≤ delta) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu)
    (raw : ActualPrescribedSpatialRawProfiles F hF c chi nu a W K n j ell Mg Bchi Bnu)
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (kappa : Y → Ep × M) (Omega S : Set Y) (hOmega : IsOpen Omega) (hS : S ⊆ Omega)
    (hsource : MapsTo kappa Omega a.source)
    (htransition : ContDiffOn ℝ ∞ (a ∘ kappa) Omega)
    (hsample : ∀ y ∈ S, a (kappa y) ∈ raw.sample)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (htransitionb : ∀ k, 1 ≤ k → k ≤ j → ∀ y ∈ S,
      ell^(k-1)*‖iteratedFDeriv ℝ k (a ∘ kappa) y‖ ≤ T k)
    (u : Fin p → ℝ) :
    let vf := actualProbeNormalAmplitude F c chi nu delta tau lam
    let amp := round4PrescribedGlobalAmplitude imag label l F hF c vf tau length a u
    let C := round4ObservationJetCost T j * round4PrescribedAmplitudeJetCost m N n length j imag lam Mg Bchi Bnu
    tsupport (fun z : W => amp z) ⊆ Subtype.val ⁻¹' K ∧
    ContDiffOn ℝ ∞ (amp ∘ kappa) Omega ∧ ∀ k ≤ j, ∀ y ∈ S,
      ell^k*‖iteratedFDeriv ℝ k (amp ∘ kappa) y‖ ≤ C*delta*tau*‖u‖ := by
  intro vf amp C
  have hvf : ContDiffOn ℝ ∞ (fun z : X => (vf z.1 z.2 : V)) a.target :=
    (raw.cutoff_smooth.smul raw.normal_smooth).const_smul (-(delta*tau)/lam^2)
  have hinput : ∀ z ∈ a.target, z ∈ tsupport (fun w : X => (vf w.1 w.2 : V)) → a.symm z ∈ K := by
    intro z hz hn
    apply raw.cutoff_support z hz
    exact ((tsupport_smul_subset_right _ _).trans (tsupport_smul_subset_left _ _)) hn
  have hsupp := (round4_prescribed_global_amplitude_smooth imag label l F hF c vf tau length a W K
    hW raw.closed_support raw.support_source raw.chart_smooth raw.A_smooth raw.B_smooth raw.G_smooth
    raw.J_smooth raw.T_smooth raw.BR_smooth hvf hinput u).2
  refine ⟨hsupp, ?_⟩
  exact round4_prescribed_global_amplitude_observation_jets imag label l F hF c chi nu
    n length j horder a.target raw.sample a.open_target raw.sample_subset
    raw.A_smooth raw.B_smooth raw.G_smooth raw.J_smooth raw.T_smooth raw.BR_smooth
    raw.cutoff_smooth raw.normal_smooth tau ell delta lam Mg Bchi Bnu htau htaul hell1
    hMg hdelta hBchi hBnu raw.A_jets raw.B_jets raw.G_jets raw.J_jets raw.T_jets
    raw.BR_jets raw.cutoff_jets raw.normal_jets a Subset.rfl kappa Omega S hOmega hS
    hsource htransition hsample T hT htransitionb u

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_prescribed_amplitude_from_raw
