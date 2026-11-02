import GlobalEmbedding.Offline.SpatialSmoothingJets
import GlobalEmbedding.Offline.LocalKernelGain

/-!
# True spatial-jet derivative gain with joint source/parameter derivatives

Source: `main.tex` 700–720 and the parameter/source convention of (6.2).
The initial first and second derivatives below are literal spatial slice
derivatives. Every additional derivative is in the full joint space. Their
input bounds are only the true spatial jet values on the sampling buffer;
there is no extra pure parameter derivative in the base norm. The actual
same joint convolution, with no globally integrable source assumption, is
used throughout. Original packet-norm comparison and global parameter-chart
gluing remain separate interfaces.
-/

open MeasureTheory GlobalEmbedding.Paper Filter
open scoped ContDiff Topology

namespace GlobalEmbedding.Offline

noncomputable section

variable {Ep Es Y : Type*}
    [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [FiniteDimensional ℝ Ep]
    [NormedAddCommGroup Es] [NormedSpace ℝ Es] [FiniteDimensional ℝ Es]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [MeasurableSpace Ep] [BorelSpace Ep] [MeasurableSpace Es] [BorelSpace Es]
    (mu : Measure (Ep × Es)) [mu.IsAddHaarMeasure]

/-- Additional joint derivatives of the SAME smoothed first spatial jet cost
ell^-j times only the first spatial source-jet bound on the actual buffer. -/
theorem signedSmoothing_spatial_first_gain {K : (Ep × Es) → ℝ}
    (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {u : Ep × Es → Y} {U V : Set (Ep × Es)} (hU : IsOpen U) (hV : IsOpen V)
    (hu : ContDiffOn ℝ ∞ u V) {ell : ℝ} (hell : 0 < ell)
    (hbuffer : ∀ z ∈ U, ∀ y ∈ tsupport K, z - ell • y ∈ V)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ w ∈ V, ‖fderiv ℝ (fun x : Es => u (w.1, x)) w.2‖ ≤ B)
    (j : ℕ) {z : Ep × Es} (hz : z ∈ U) :
    ‖iteratedFDeriv ℝ j (fun w : Ep × Es =>
      fderiv ℝ (fun x : Es => signedSmoothing mu K ell u (w.1, x)) w.2) z‖ ≤
      B * (ell⁻¹)^j * ∫ y, ‖iteratedFDeriv ℝ j K y‖ ∂mu := by
  have heq : (fun w : Ep × Es =>
      fderiv ℝ (fun x : Es => signedSmoothing mu K ell u (w.1, x)) w.2) =ᶠ[𝓝 z]
      signedSmoothing mu K ell (fun w : Ep × Es => fderiv ℝ (fun x : Es => u (w.1, x)) w.2) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact signedSmoothing_spatial_fderiv mu hK hcompact hU hV hu ell hbuffer hw
  rw [(heq.iteratedFDeriv ℝ j).eq_of_nhds]
  exact signedSmoothing_local_derivative_gain mu hK hcompact hU hV
    (incrementsJointSpatialJets_bridge u V hV hu).2.1.continuousOn hell hbuffer B hB hbound j hz

/-- Additional joint derivatives of the SAME smoothed second spatial jet cost
ell^-j times only the second spatial source-jet bound. In particular, there is
no hypothesis on two pure parameter derivatives of u at base order zero. -/
theorem signedSmoothing_spatial_second_gain {K : (Ep × Es) → ℝ}
    (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {u : Ep × Es → Y} {U V : Set (Ep × Es)} (hU : IsOpen U) (hV : IsOpen V)
    (hu : ContDiffOn ℝ ∞ u V) {ell : ℝ} (hell : 0 < ell)
    (hbuffer : ∀ z ∈ U, ∀ y ∈ tsupport K, z - ell • y ∈ V)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ w ∈ V, ‖fderiv ℝ (fderiv ℝ (fun x : Es => u (w.1, x))) w.2‖ ≤ B)
    (j : ℕ) {z : Ep × Es} (hz : z ∈ U) :
    ‖iteratedFDeriv ℝ j (fun w : Ep × Es =>
      fderiv ℝ (fderiv ℝ (fun x : Es => signedSmoothing mu K ell u (w.1, x))) w.2) z‖ ≤
      B * (ell⁻¹)^j * ∫ y, ‖iteratedFDeriv ℝ j K y‖ ∂mu := by
  have heq : (fun w : Ep × Es =>
      fderiv ℝ (fderiv ℝ (fun x : Es => signedSmoothing mu K ell u (w.1, x))) w.2) =ᶠ[𝓝 z]
      signedSmoothing mu K ell
        (fun w : Ep × Es => fderiv ℝ (fderiv ℝ (fun x : Es => u (w.1, x))) w.2) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact signedSmoothing_spatial_second_fderiv mu hK hcompact hU hV hu ell hbuffer hw
  rw [(heq.iteratedFDeriv ℝ j).eq_of_nhds]
  exact signedSmoothing_local_derivative_gain mu hK hcompact hU hV
    (incrementsJointSpatialJets_bridge u V hV hu).2.2.continuousOn hell hbuffer B hB hbound j hz

end

end GlobalEmbedding.Offline
