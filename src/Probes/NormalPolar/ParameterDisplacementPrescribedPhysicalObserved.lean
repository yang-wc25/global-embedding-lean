import NormalPolar.ParameterDisplacementPrescribedPhysicalNative
import Probes.Round4PrescribedReconstructedColumns

/-!
# The same prescribed physical residual in the actual observation chart

Both spatial Jacobian slots are transported. The complete global amplitude
extensions give the support, including zero germs outside the carrier. The
physical residual and its jets are derived from the native finite solver.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold Filter GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology Classical
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

private local instance prescribedObsTensorSemi : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance prescribedObsTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance prescribedObsTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

def actualPrescribedPhysicalPiece
    (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b)) (c : Ep → D → M)
    (vf : (b : Ep) → (x : D) → normalSpace (I := IM) (F b) (c b x))
    (phase : Ep × M → ℝ) (tau : ℝ) (length : ℕ) (a : OpenPartialHomeomorph (Ep × M) X)
    (u : Fin p → ℝ) (z : Ep × M) : V :=
  Real.cos (phase z/tau) • round4PrescribedGlobalAmplitude false label l F hF c vf tau length a u z -
    Real.sin (phase z/tau) • round4PrescribedGlobalAmplitude true label l F hF c vf tau length a u z

theorem actual_prescribed_raw_observed_physical
    (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (c : Ep → D → M) (chi : X → ℝ)
    (nu : (b : Ep) → (x : D) → normalSpace (I := IM) (F b) (c b x))
    (a : OpenPartialHomeomorph (Ep × M) X) (W K : Set (Ep × M)) (hW : IsOpen W) (phase : Ep × M → ℝ)
    (n length j : ℕ) (horder : j+length ≤ n)
    (tau ell delta lam Mg Bchi Bnu : ℝ)
    (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hdelta : 0 ≤ delta) (hlam : lam ≠ 0) (hMg : 0 ≤ Mg) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu)
    (raw : ActualPrescribedSpatialRawProfiles F hF c chi nu a W K n (j+1) ell Mg Bchi Bnu)
    (geom : ActualPrescribedPhysicalGeometry F hF c nu a phase)
    (kappa : Y → Ep × M) (parameter : Eq → Ep) (O S : Set Y) (hO : IsOpen O) (hS : S ⊆ O)
    (hsource : MapsTo kappa O a.source) (hfirst : ∀ z ∈ O, (kappa z).1 = parameter z.1)
    (htransition : ContDiffOn ℝ ∞ (a ∘ kappa) O)
    (hsample : ∀ z ∈ S, a (kappa z) ∈ raw.sample)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (htransitionb : ∀ z ∈ S, ∀ k, 1 ≤ k → k ≤ j+1 →
      ell^(k-1)*‖iteratedFDeriv ℝ k (a ∘ kappa) z‖ ≤ T k)
    (u : Fin p → ℝ) :
    let vf := actualProbeNormalAmplitude F c chi nu delta tau lam
    let piece := actualPrescribedPhysicalPiece label l F hF c vf phase tau length a u
    let Fobs := fun z : Y => F (kappa z).1 (kappa z).2
    let E := actualJointMetricLinearization Fobs (piece ∘ kappa)
    let Kn := probeNormalAmplitudeConstant n lam Bchi Bnu
    let C := actualFastTensorChartTransferPrefix T j * actualPrimaryPhysicalCost m N n length j Mg Kn Kn
    tsupport (fun z : W => piece z) ⊆ Subtype.val ⁻¹' K ∧
    ContDiffOn ℝ ∞ (piece ∘ kappa) O ∧ ContDiffOn ℝ ∞ E O ∧
      ∀ k ≤ j, ∀ z ∈ S, tau^k*‖iteratedFDeriv ℝ k E z‖ ≤ C*(tau/ell)^length*(delta*tau)*‖u‖ := by
  intro vf piece Fobs E Kn C
  have hvf : ContDiffOn ℝ ∞ (fun z : X => (vf z.1 z.2 : V)) a.target :=
    (raw.cutoff_smooth.smul raw.normal_smooth).const_smul (-(delta*tau)/lam^2)
  have hinput : ∀ z ∈ a.target, z ∈ tsupport (fun w : X => (vf w.1 w.2 : V)) → a.symm z ∈ K := by
    intro z hz hn
    apply raw.cutoff_support z hz
    exact ((tsupport_smul_subset_right _ _).trans (tsupport_smul_subset_left _ _)) hn
  have hsupp (ch : Bool) := (round4_prescribed_global_amplitude_smooth ch label l F hF c vf tau length a W K
    hW raw.closed_support raw.support_source raw.chart_smooth raw.A_smooth raw.B_smooth raw.G_smooth
    raw.J_smooth raw.T_smooth raw.BR_smooth hvf hinput u).2
  have hsupport : tsupport (fun z : W => piece z) ⊆ Subtype.val ⁻¹' K := by
    apply (tsupport_sub _ _).trans
    apply union_subset
    · exact (tsupport_smul_subset_right _ _).trans (hsupp false)
    · exact (tsupport_smul_subset_right _ _).trans (hsupp true)
  let mode := fun z : X => round4ActualProbeMode label l (F z.1) (hF z.1) (c z.1)
    (vf z.1) (fun x => x 0) tau length u z.2
  let Elocal := fun z : X => actualCoordinateMetricLinearization (F z.1 ∘ c z.1) (fun x => mode (z.1,x)) z.2
  have hp := actual_prescribed_raw_native_physical label l F hF c chi nu a W K phase n length j horder
    tau ell delta lam Mg Bchi Bnu htau htaul hell1 hdelta hlam hMg hBchi hBnu raw geom u
  have hmap : MapsTo (a ∘ kappa) O a.target := fun z hz => a.map_source (hsource hz)
  have hvalue (z : Y) (hz : z ∈ O) : piece (kappa z) = mode (a (kappa z)) := by
    dsimp only [piece,actualPrescribedPhysicalPiece,mode,round4PrescribedGlobalAmplitude]
    simp only [if_pos (hsource hz),geom.adaptation (kappa z) (hsource hz)]
    exact (round4ActualProbeMode_eq_amplitudes label l (F (a (kappa z)).1) (hF (a (kappa z)).1)
      (c (a (kappa z)).1) (vf (a (kappa z)).1) (fun x => x 0) tau length u (a (kappa z)).2).symm
  have hreg : ContDiffOn ℝ ∞ (piece ∘ kappa) O := (hp.1.comp htransition hmap).congr hvalue
  have he := actual_observed_linearization_source_coordinates F hF c a geom.slices geom.maximal geom.coordinates
    geom.target geom.inverse piece mode hp.1 kappa parameter O hO hsource hfirst htransition hvalue
  have hEreg : ContDiffOn ℝ ∞ E O :=
    (actual_joint_native_tensor_pullback_contDiffOn (a ∘ kappa) Elocal O a.target hO htransition hp.2.1 hmap).congr he
  refine ⟨hsupport,hreg,hEreg,?_⟩
  intro k hk z hz
  let Cnative := actualPrimaryPhysicalCost m N n length j Mg Kn Kn * (tau/ell)^length*(delta*tau)*‖u‖
  have hKn : 0 ≤ Kn := probeNormalAmplitudeConstant_nonneg n lam hBchi hBnu
  have hCp : 0 ≤ actualPrimaryPhysicalCost m N n length j Mg Kn Kn :=
    actualPrimaryPhysicalCost_nonneg m N n length j hMg hKn hKn
  have hell : 0 < ell := htau.trans_le htaul
  have hCnative : 0 ≤ Cnative := by dsimp only [Cnative]; positivity
  have hb := (actual_fast_joint_tensor_chart_transfer T hT k (a ∘ kappa) Elocal O a.target hO a.open_target
    htransition hp.2.1 hmap z (hS hz) tau ell Cnative htau htaul hCnative
    (fun q hq => hp.2.2 q (hq.trans hk) _ (hsample z hz))
    (fun q hq hqk => htransitionb z hz q hq (by omega))).2
  have hnear := he.eventuallyEq_of_mem (hO.mem_nhds (hS hz))
  rw [(hnear.iteratedFDeriv ℝ k).eq_of_nhds]
  exact hb.trans ((mul_le_mul_of_nonneg_right (actualFastTensorChartTransferCost_le_prefix T hT hk) hCnative).trans_eq
    (by dsimp only [C,Cnative]; ring))

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_prescribed_raw_observed_physical
