import GlobalEmbedding.Offline.LocalSmoothingEstimates
import GlobalEmbedding.Paper.IncrementsJointSpatialJets

/-!
# Literal spatial jets commute with the same joint smoothing

Source: `literature/parallelizable-stable-plus-one/main.tex`, equation
(6.4), lines 704–719, and the parameter/spatial convention in (6.2).
The source is a genuine joint map on `Ep × Es`. Every spatial derivative
below is the native Fréchet derivative of its literal `Es` slice. The
kernel samples the joint parameter/source domain, and all regularity is
local to the open buffer. The existing original joint-spatial-jet bridge
supplies regularity of the true source jet fields.
-/

open MeasureTheory GlobalEmbedding.Paper
open scoped ContDiff Topology

namespace GlobalEmbedding.Offline

noncomputable section

variable {Ep Es Y : Type*}
    [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [FiniteDimensional ℝ Ep]
    [NormedAddCommGroup Es] [NormedSpace ℝ Es] [FiniteDimensional ℝ Es]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [MeasurableSpace Ep] [BorelSpace Ep] [MeasurableSpace Es] [BorelSpace Es]
    (mu : Measure (Ep × Es)) [mu.IsAddHaarMeasure]

/-- The first literal spatial derivative of the actual joint smoothing
is smoothing of the literal spatial derivative. No parameter derivative
is substituted for this native slice derivative. -/
theorem signedSmoothing_spatial_fderiv {K : (Ep × Es) → ℝ}
    (hK : ContDiff ℝ ∞ K) (hKcompact : HasCompactSupport K)
    {u : Ep × Es → Y} {U V : Set (Ep × Es)} (hU : IsOpen U) (hV : IsOpen V)
    (hu : ContDiffOn ℝ ∞ u V) (ell : ℝ)
    (hbuffer : ∀ z ∈ U, ∀ y ∈ tsupport K, z - ell • y ∈ V)
    {z : Ep × Es} (hz : z ∈ U) :
    fderiv ℝ (fun x : Es => signedSmoothing mu K ell u (z.1, x)) z.2 =
      signedSmoothing mu K ell
        (fun w : Ep × Es => fderiv ℝ (fun x : Es => u (w.1, x)) w.2) z := by
  let Us := (fun x : Es => (z.1, x)) ⁻¹' U
  have hUs : IsOpen Us := hU.preimage (continuous_const.prodMk continuous_id)
  have hzUs : z.2 ∈ Us := hz
  have hfamily : ContDiffOn ℝ ∞
      (fun w : Es × (Ep × Es) => K w.2 • u ((z.1, w.1) - ell • w.2))
      (Us ×ˢ Set.univ) := by
    have h := smoothingFamily_contDiffOn hK hV hu ell hbuffer
    exact h.comp ((contDiffOn_const.prodMk contDiffOn_fst).prodMk contDiffOn_snd)
      (fun w hw => ⟨hw.1, trivial⟩)
  have hd := hasFDerivAt_compactIntegral mu hUs hKcompact
    (f := fun x y => K y • u ((z.1, x) - ell • y))
    (by
      intro x hx y hy
      simp only [image_eq_zero_of_notMem_tsupport hy, zero_smul])
    (hfamily.of_le (by simp)) hzUs
  change HasFDerivAt (fun x : Es => signedSmoothing mu K ell u (z.1, x)) _ z.2 at hd
  rw [hd.fderiv]
  unfold signedSmoothing
  apply integral_congr_ae
  filter_upwards [] with y
  change fderiv ℝ (K y • (fun x : Es => u (z.1 - ell • y.1, x - ell • y.2))) z.2 = _
  rw [fderiv_const_smul_field (𝕜 := ℝ)
    (f := fun x : Es => u (z.1 - ell • y.1, x - ell • y.2)) (K y)]
  change K y • fderiv ℝ (fun x : Es => u (z.1 - ell • y.1, x - ell • y.2)) z.2 = _
  rw [fderiv_comp_sub (𝕜 := ℝ) (f := fun x : Es => u (z.1 - ell • y.1, x)) (ell • y.2)]
  rfl

/-- The second literal spatial derivative also commutes with the same
joint smoothing. The first spatial-jet field is smooth by the original
local joint/spatial bridge, and equality on the open output slice lets
one differentiate the first commutation identity. -/
theorem signedSmoothing_spatial_second_fderiv {K : (Ep × Es) → ℝ}
    (hK : ContDiff ℝ ∞ K) (hKcompact : HasCompactSupport K)
    {u : Ep × Es → Y} {U V : Set (Ep × Es)} (hU : IsOpen U) (hV : IsOpen V)
    (hu : ContDiffOn ℝ ∞ u V) (ell : ℝ)
    (hbuffer : ∀ z ∈ U, ∀ y ∈ tsupport K, z - ell • y ∈ V)
    {z : Ep × Es} (hz : z ∈ U) :
    fderiv ℝ (fderiv ℝ (fun x : Es => signedSmoothing mu K ell u (z.1, x))) z.2 =
      signedSmoothing mu K ell
        (fun w : Ep × Es => fderiv ℝ (fderiv ℝ (fun x : Es => u (w.1, x))) w.2) z := by
  let u₁ := fun w : Ep × Es => fderiv ℝ (fun x : Es => u (w.1, x)) w.2
  have hu₁ : ContDiffOn ℝ ∞ u₁ V := (incrementsJointSpatialJets_bridge u V hV hu).2.1
  let Us := (fun x : Es => (z.1, x)) ⁻¹' U
  have hUs : IsOpen Us := hU.preimage (continuous_const.prodMk continuous_id)
  have heq : fderiv ℝ (fun x : Es => signedSmoothing mu K ell u (z.1, x)) =ᶠ[nhds z.2]
      (fun x : Es => signedSmoothing mu K ell u₁ (z.1, x)) := by
    filter_upwards [hUs.mem_nhds hz] with x hx
    exact signedSmoothing_spatial_fderiv mu hK hKcompact hU hV hu ell hbuffer hx
  rw [heq.fderiv_eq]
  exact signedSmoothing_spatial_fderiv mu hK hKcompact hU hV hu₁ ell hbuffer hz

end

end GlobalEmbedding.Offline
