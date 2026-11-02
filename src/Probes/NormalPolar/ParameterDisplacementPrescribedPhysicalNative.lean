import NormalPolar.ParameterDisplacementPrescribedPhysicalCoordinates

/-! The actual prescribed normal source produces the full native physical
linearized-metric residual through the original finite reconstruction. -/

noncomputable section
open Set Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {m N p r : ℕ} {Ep M : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "IM" => 𝓘(ℝ,D)

private local instance prescribedNativeTensorSemi : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance prescribedNativeTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance prescribedNativeTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem actual_prescribed_raw_native_physical
    (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (c : Ep → D → M) (chi : X → ℝ)
    (nu : (b : Ep) → (x : D) → normalSpace (I := IM) (F b) (c b x))
    (a : OpenPartialHomeomorph (Ep × M) X) (W K : Set (Ep × M)) (phase : Ep × M → ℝ)
    (n length j : ℕ) (horder : j+length ≤ n)
    (tau ell delta lam Mg Bchi Bnu : ℝ)
    (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hdelta : 0 ≤ delta) (hlam : lam ≠ 0) (hMg : 0 ≤ Mg) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu)
    (raw : ActualPrescribedSpatialRawProfiles F hF c chi nu a W K n (j+1) ell Mg Bchi Bnu)
    (geom : ActualPrescribedPhysicalGeometry F hF c nu a phase)
    (u : Fin p → ℝ) :
    let vf := actualProbeNormalAmplitude F c chi nu delta tau lam
    let mode := fun z : X => round4ActualProbeMode label l (F z.1) (hF z.1) (c z.1)
      (vf z.1) (fun x => x 0) tau length u z.2
    let E := fun z : X => actualCoordinateMetricLinearization (F z.1 ∘ c z.1)
      (fun x => mode (z.1,x)) z.2
    let Kn := probeNormalAmplitudeConstant n lam Bchi Bnu
    ContDiffOn ℝ ∞ mode a.target ∧ ContDiffOn ℝ ∞ E a.target ∧
      ∀ k ≤ j, ∀ z ∈ raw.sample, tau^k*‖iteratedFDeriv ℝ k E z‖ ≤
        actualPrimaryPhysicalCost m N n length j Mg Kn Kn * (tau/ell)^length * (delta*tau)*‖u‖ := by
  intro vf mode E Kn
  have hid (x : D) : lam * (x 0 / lam) = x 0 := by field_simp
  have hp := round4_prescribed_mode_physical_residual label l F hF geom.slices geom.maximal c geom.coordinates
    (fun z : X => z.2 0 / lam) chi nu a.target raw.sample a.open_target raw.sample_subset
    geom.target geom.immersion geom.gram geom.normal_kernel raw.cutoff_smooth raw.normal_smooth
    raw.BR_smooth raw.A_smooth raw.B_smooth raw.G_smooth raw.J_smooth raw.T_smooth n length j horder
    tau ell delta lam Mg Bchi Bnu htau htaul hell1 hdelta hMg hBchi hBnu
    (fun z _ => hid z.2)
    (fun k hk z hz => raw.BR_jets k hk z (raw.sample_subset hz)) raw.A_jets raw.B_jets raw.cutoff_jets raw.normal_jets u
  simpa only [hid] using hp

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_prescribed_raw_native_physical
