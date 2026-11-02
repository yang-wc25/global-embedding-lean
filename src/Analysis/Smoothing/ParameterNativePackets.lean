import Smoothing.ParameterJetIdentities
import GlobalEmbedding.Offline.SpatialSmoothingJets
import GlobalEmbedding.Offline.LocalKernelGain

/-!
# The true native spatial packet: locality, sums and convolution

Every object is a derivative of one joint map. Locality and finite-sum laws
allow support multiplicity to control global gluing. Convolution commutation
and gain use only spatial C2 input; parameter derivatives remain additional.
-/

open GlobalEmbedding.Offline GlobalEmbedding.Paper Function Filter Set MeasureTheory
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation
noncomputable section

variable {Ep Es Y : Type*}
    [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
    [NormedAddCommGroup Es] [NormedSpace ℝ Es]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Equality of the original map germ determines its actual spatial two-jet. -/
theorem spatialNativeJet_eq_of_eventuallyEq {f g : Ep × Es → Y} {z : Ep × Es}
    (h : f =ᶠ[𝓝 z] g) : spatialNativeJet f z = spatialNativeJet g z := by
  have hs : (fun x => f (z.1,x)) =ᶠ[𝓝 z.2] (fun x => g (z.1,x)) :=
    h.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
  apply Prod.ext h.eq_of_nhds
  apply Prod.ext hs.fderiv_eq
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  simpa only [spatialNativeJet, iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] using congrArg (fun L => L ![v,w])
      ((hs.iteratedFDeriv ℝ 2).eq_of_nhds)

/-- A zero germ of a localized map is a zero germ of its genuine spatial packet. -/
theorem spatialNativeJet_eventuallyEq {f g : Ep × Es → Y} {z : Ep × Es}
    (h : f =ᶠ[𝓝 z] g) : spatialNativeJet f =ᶠ[𝓝 z] spatialNativeJet g :=
  h.eventuallyEq_nhds.mono (fun _ h' => spatialNativeJet_eq_of_eventuallyEq h')

@[simp] theorem spatialNativeJet_zero : spatialNativeJet (fun _ : Ep × Es => (0 : Y)) = 0 := by
  funext z
  simp [spatialNativeJet, Prod.fst_sum, Prod.snd_sum]

/-- The finite packet sum is exactly the packet of the same finite map sum. -/
theorem spatialNativeJet_sum {ι : Type*} [Fintype ι]
    (f : ι → Ep × Es → Y) {z : Ep × Es}
    (hf : ∀ i, ContDiffAt ℝ ∞ (f i) z) :
    spatialNativeJet (fun x => ∑ i, f i x) z = ∑ i, spatialNativeJet (f i) z := by
  classical
  have hs (i : ι) : ContDiffAt ℝ ∞ (fun x => f i (z.1,x)) z.2 :=
    (hf i).comp z.2 (contDiffAt_const.prodMk contDiffAt_id)
  apply Prod.ext
  · simp [spatialNativeJet, Prod.fst_sum, Prod.snd_sum]
  apply Prod.ext
  · change fderiv ℝ (fun x => ∑ i, f i (z.1,x)) z.2 = _
    rw [fderiv_fun_sum (fun i _ => (hs i).differentiableAt (by simp))]
    simp [spatialNativeJet, Prod.fst_sum, Prod.snd_sum]
  · apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    have h := congrArg (fun L => L ![v,w])
      (iteratedFDeriv_fun_sum_apply (n := 2)
        (fun i (_ : i ∈ (Finset.univ : Finset ι)) => (hs i).of_le (by simp)))
    simpa [spatialNativeJet, Prod.fst_sum, Prod.snd_sum, iteratedFDeriv_two_apply] using h

/-- Subtraction likewise preserves the actual derivative packet. -/
theorem spatialNativeJet_sub {f g : Ep × Es → Y} {z : Ep × Es}
    (hf : ContDiffAt ℝ ∞ f z) (hg : ContDiffAt ℝ ∞ g z) :
    spatialNativeJet (fun y => f y - g y) z = spatialNativeJet f z - spatialNativeJet g z := by
  have hfs : ContDiffAt ℝ ∞ (fun x => f (z.1,x)) z.2 :=
    hf.comp z.2 (contDiffAt_const.prodMk contDiffAt_id)
  have hgs : ContDiffAt ℝ ∞ (fun x => g (z.1,x)) z.2 :=
    hg.comp z.2 (contDiffAt_const.prodMk contDiffAt_id)
  apply Prod.ext
  · rfl
  apply Prod.ext
  · exact fderiv_fun_sub (hfs.differentiableAt (by simp)) (hgs.differentiableAt (by simp))
  · apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    have hraw : iteratedFDeriv ℝ 2 (fun x => f (z.1,x) - g (z.1,x)) z.2 =
        iteratedFDeriv ℝ 2 (fun x => f (z.1,x)) z.2 -
          iteratedFDeriv ℝ 2 (fun x => g (z.1,x)) z.2 :=
      iteratedFDeriv_sub_apply (i := 2) (hfs.of_le (by simp)) (hgs.of_le (by simp))
    simpa [spatialNativeJet, iteratedFDeriv_two_apply] using
      congrArg (fun L => L ![v,w]) hraw

section Convolution
variable [FiniteDimensional ℝ Ep] [FiniteDimensional ℝ Es] [CompleteSpace Y]
    [MeasurableSpace Ep] [BorelSpace Ep] [MeasurableSpace Es] [BorelSpace Es]
    (mu : Measure (Ep × Es)) [mu.IsAddHaarMeasure]

/-- Integrability follows from the true common compact kernel support. -/
theorem parameter_smoothing_integrable {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Ep × Es → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {f : Ep × Es → F} {U V : Set (Ep × Es)} (hV : IsOpen V)
    (hf : ContDiffOn ℝ ∞ f V) (ell : ℝ)
    (hbuffer : ∀ z ∈ U, ∀ y ∈ tsupport K, z - ell • y ∈ V)
    {z : Ep × Es} (hz : z ∈ U) :
    Integrable (fun y => K y • f (z - ell • y)) mu := by
  have hc : Continuous (fun y => K y • f (z - ell • y)) :=
    (smoothingFamily_contDiffOn hK hV hf ell hbuffer).continuousOn.comp_continuous
      (continuous_const.prodMk continuous_id) (fun y => ⟨hz, trivial⟩)
  have hs : HasCompactSupport (fun y => K y • f (z - ell • y)) :=
    hcompact.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_left _ _)
  exact hc.integrable_of_hasCompactSupport hs

/-- All three entries commute with the very same joint convolution. -/
theorem spatialNativeJet_smoothing {K : Ep × Es → ℝ}
    (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {u : Ep × Es → Y} {U V : Set (Ep × Es)} (hU : IsOpen U) (hV : IsOpen V)
    (hu : ContDiffOn ℝ ∞ u V) (ell : ℝ)
    (hbuffer : ∀ z ∈ U, ∀ y ∈ tsupport K, z - ell • y ∈ V)
    {z : Ep × Es} (hz : z ∈ U) :
    spatialNativeJet (signedSmoothing mu K ell u) z =
      signedSmoothing mu K ell (spatialNativeJet u) z := by
  have hj := incrementsJointSpatialJets_bridge u V hV hu
  have hI0 := parameter_smoothing_integrable mu hK hcompact hV hu ell hbuffer hz
  have hI1 := parameter_smoothing_integrable mu hK hcompact hV hj.2.1 ell hbuffer hz
  have hI2 := parameter_smoothing_integrable mu hK hcompact hV hj.2.2 ell hbuffer hz
  have hpair := integral_pair (E := Y)
    (F := (Es →L[ℝ] Y) × (Es →L[ℝ] Es →L[ℝ] Y)) hI0 (hI1.prodMk hI2)
  rw [integral_pair (E := Es →L[ℝ] Y) (F := Es →L[ℝ] Es →L[ℝ] Y) hI1 hI2] at hpair
  change signedSmoothing mu K ell (spatialNativeJet u) z = _ at hpair
  rw [hpair]
  apply Prod.ext
  · rfl
  apply Prod.ext
  · exact signedSmoothing_spatial_fderiv mu hK hcompact hU hV hu ell hbuffer hz
  · exact signedSmoothing_spatial_second_fderiv mu hK hcompact hU hV hu ell hbuffer hz

/-- Genuine derivative gain with only the source spatial two-jet bounded.
No pure parameter derivative is required in the base bound. -/
theorem spatialNativeJet_local_gain {K : Ep × Es → ℝ}
    (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {u : Ep × Es → Y} {U V : Set (Ep × Es)} (hU : IsOpen U) (hV : IsOpen V)
    (hu : ContDiffOn ℝ ∞ u V) {ell : ℝ} (hell : 0 < ell)
    (hbuffer : ∀ z ∈ U, ∀ y ∈ tsupport K, z - ell • y ∈ V)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ y ∈ V, ‖spatialNativeJet u y‖ ≤ B)
    (j : ℕ) {z : Ep × Es} (hz : z ∈ U) :
    ‖iteratedFDeriv ℝ j (spatialNativeJet (signedSmoothing mu K ell u)) z‖ ≤
      B * (ell⁻¹)^j * ∫ y, ‖iteratedFDeriv ℝ j K y‖ ∂mu := by
  have hcomm : spatialNativeJet (signedSmoothing mu K ell u) =ᶠ[𝓝 z]
      signedSmoothing mu K ell (spatialNativeJet u) := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact spatialNativeJet_smoothing mu hK hcompact hU hV hu ell hbuffer hy
  rw [(hcomm.iteratedFDeriv ℝ j).eq_of_nhds]
  exact signedSmoothing_local_derivative_gain mu hK hcompact hU hV
    (spatialNativeJet_contDiffOn hV hu).continuousOn hell hbuffer B hB hbound j hz

/-- The spatial packet of the actual error is locally the error in smoothing
that same source packet; this equality is proved before differentiating. -/
theorem spatialNativeJet_error_eventuallyEq {K : Ep × Es → ℝ}
    (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {u : Ep × Es → Y} {U V : Set (Ep × Es)} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ⊆ V) (hu : ContDiffOn ℝ ∞ u V) (ell : ℝ)
    (hbuffer : ∀ z ∈ U, ∀ y ∈ tsupport K, z - ell • y ∈ V)
    {z : Ep × Es} (hz : z ∈ U) :
    spatialNativeJet (fun y => signedSmoothing mu K ell u y - u y) =ᶠ[𝓝 z]
      (fun y => signedSmoothing mu K ell (spatialNativeJet u) y - spatialNativeJet u y) := by
  have hs := signedSmoothing_contDiffOn mu hK hcompact hU hV hu ell hbuffer
  filter_upwards [hU.mem_nhds hz] with y hy
  rw [spatialNativeJet_sub (hs.contDiffAt (hU.mem_nhds hy))
    (hu.contDiffAt (hV.mem_nhds (hUV hy))),
    spatialNativeJet_smoothing mu hK hcompact hU hV hu ell hbuffer hy]

/-- Cumulative low Taylor estimate with precisely r joint derivatives of the
source spatial two-jet, including the borderline j=r. -/
theorem spatialNativeJet_local_low {kappa : Ep × Es → ℝ}
    (hsmooth : ContDiff ℝ ∞ kappa) (hcompact : HasCompactSupport kappa)
    (hmass : (∫ y, kappa y ∂mu) = 1) (r j : ℕ) (hjr : j ≤ r)
    {u : Ep × Es → Y} {U V : Set (Ep × Es)} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ⊆ V) (hu : ContDiffOn ℝ ∞ u V) {ell : ℝ} (hell : 0 ≤ ell)
    (hsegments : ∀ z ∈ U, ∀ y ∈ tsupport (finiteMomentKernel r kappa),
      ∀ t ∈ Set.Icc (0 : ℝ) 1, z - t • (ell • y) ∈ V)
    (B : ℝ) (hB : 0 ≤ B)
    (hsource : ∀ a ≤ r, ∀ y ∈ V, ‖iteratedFDeriv ℝ a (spatialNativeJet u) y‖ ≤ B)
    {k : ℕ} (hk : k ≤ j) {z : Ep × Es} (hz : z ∈ U) :
    ‖iteratedFDeriv ℝ k (spatialNativeJet (fun y =>
      signedSmoothing mu (finiteMomentKernel r kappa) ell u y - u y)) z‖ ≤
      kernelTailConstant mu (finiteMomentKernel r kappa) r * B * ell^(r-j) := by
  have hbuffer : ∀ z ∈ U, ∀ y ∈ tsupport (finiteMomentKernel r kappa), z - ell • y ∈ V := by
    intro z hz y hy
    simpa only [one_smul] using hsegments z hz y hy 1 (by simp)
  rw [((spatialNativeJet_error_eventuallyEq mu (finiteMomentKernel_contDiff hsmooth r)
    (finiteMomentKernel_hasCompactSupport hcompact r) hU hV hUV hu ell hbuffer hz).iteratedFDeriv ℝ k).eq_of_nhds]
  exact signedSmoothing_low_shifted_derivative_error_le mu hsmooth hcompact hmass 0 r j hjr
    hU hV hUV (spatialNativeJet_contDiffOn hV hu) hell hsegments B hB hsource hk hz

/-- High derivatives use the same-order signed-L1 estimate, still on the
actual spatial packet of the same convolution error. -/
theorem spatialNativeJet_local_high {K : Ep × Es → ℝ}
    (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {u : Ep × Es → Y} {U V : Set (Ep × Es)} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ⊆ V) (hu : ContDiffOn ℝ ∞ u V) (ell : ℝ)
    (hbuffer : ∀ z ∈ U, ∀ y ∈ tsupport K, z - ell • y ∈ V)
    (j : ℕ) (B : ℝ)
    (hsource : ∀ y ∈ V, ‖iteratedFDeriv ℝ j (spatialNativeJet u) y‖ ≤ B)
    {z : Ep × Es} (hz : z ∈ U) :
    ‖iteratedFDeriv ℝ j (spatialNativeJet (fun y => signedSmoothing mu K ell u y - u y)) z‖ ≤
      (1 + ∫ y, |K y| ∂mu) * B := by
  rw [((spatialNativeJet_error_eventuallyEq mu hK hcompact hU hV hUV hu ell hbuffer hz).iteratedFDeriv ℝ j).eq_of_nhds]
  exact signedSmoothing_derivative_error_le_L1 mu hK hcompact hU hV hUV
    (spatialNativeJet_contDiffOn hV hu) ell hbuffer j hz B hsource

/-- Cumulative gain retains only the literal spatial C2 source packet. -/
theorem spatialNativeJet_local_cumulative_gain {K : Ep × Es → ℝ}
    (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {u : Ep × Es → Y} {U V : Set (Ep × Es)} (hU : IsOpen U) (hV : IsOpen V)
    (hu : ContDiffOn ℝ ∞ u V) {ell : ℝ} (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hbuffer : ∀ z ∈ U, ∀ y ∈ tsupport K, z - ell • y ∈ V)
    (j : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hsource : ∀ a ≤ 0, ∀ y ∈ V, ‖iteratedFDeriv ℝ a (spatialNativeJet u) y‖ ≤ B)
    {k : ℕ} (hk : k ≤ j) {z : Ep × Es} (hz : z ∈ U) :
    ‖iteratedFDeriv ℝ k (spatialNativeJet (signedSmoothing mu K ell u)) z‖ ≤
      kernelGainConstant mu K j * B * (ell⁻¹)^j := by
  have heq : spatialNativeJet (signedSmoothing mu K ell u) =ᶠ[𝓝 z]
      signedSmoothing mu K ell (spatialNativeJet u) := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact spatialNativeJet_smoothing mu hK hcompact hU hV hu ell hbuffer hy
  rw [(heq.iteratedFDeriv ℝ k).eq_of_nhds]
  exact signedSmoothing_local_cumulative_gain mu hK hcompact hU hV
    (spatialNativeJet_contDiffOn hV hu) hell hell1 hbuffer 0 j B hB hsource hk hz

#print axioms spatialNativeJet_local_low
#print axioms spatialNativeJet_local_high
#print axioms spatialNativeJet_local_cumulative_gain

end Convolution

#print axioms spatialNativeJet_eventuallyEq
#print axioms spatialNativeJet_sum
#print axioms spatialNativeJet_smoothing
#print axioms spatialNativeJet_local_gain
end
end GlobalEmbedding.Continuation
