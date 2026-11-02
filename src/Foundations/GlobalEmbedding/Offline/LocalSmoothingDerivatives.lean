import GlobalEmbedding.Offline.KernelDerivativeGain
import GlobalEmbedding.Offline.CompactParametricIntegral

/-!
# Actual smoothing derivatives on buffered open domains

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines 700–719,
and `repair-local-convolution-estimates`. The source is smooth only on
the open buffer `V`; its values away from `V` are unrestricted. Every
point sampled by the actual compact kernel from the output domain `U`
is required to lie in `V`. Parameter differentiation is justified by
the genuine compact-family integral theorem, so all derivatives below
are derivatives of the same actual convolution.
-/

open MeasureTheory
open scoped ContDiff Topology

namespace GlobalEmbedding.Offline

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (mu : Measure E) [mu.IsAddHaarMeasure]

omit [CompleteSpace F] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- The actual smoothing integrand is jointly smooth locally. Away from
the kernel's topological support it is locally zero, so no smoothness
of the source outside its buffer is needed. -/
theorem smoothingFamily_contDiffOn {K : E → ℝ} (hK : ContDiff ℝ ∞ K)
    {u : E → F} {U V : Set E} (hV : IsOpen V) (hu : ContDiffOn ℝ ∞ u V)
    (ell : ℝ) (hbuffer : ∀ x ∈ U, ∀ y ∈ tsupport K, x - ell • y ∈ V) :
    ContDiffOn ℝ ∞ (fun z : E × E => K z.2 • u (z.1 - ell • z.2))
      (U ×ˢ Set.univ) := by
  intro z hz
  by_cases hy : z.2 ∈ tsupport K
  · have huat := hu.contDiffAt (hV.mem_nhds (hbuffer z.1 hz.1 z.2 hy))
    have hmap : ContDiffAt ℝ ∞ (fun w : E × E => w.1 - ell • w.2) z :=
      contDiffAt_fst.sub (contDiffAt_const.smul contDiffAt_snd)
    exact ((hK.contDiffAt.comp z contDiffAt_snd).smul (huat.comp z hmap)).contDiffWithinAt
  · have hzero : (fun w : E × E => K w.2 • u (w.1 - ell • w.2)) =ᶠ[nhds z] 0 := by
      filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hy).comp_tendsto
        continuous_snd.continuousAt] with w hw
      change K w.2 = 0 at hw
      simp only [hw, zero_smul, Pi.zero_apply]
    exact (contDiffAt_const.congr_of_eventuallyEq hzero).contDiffWithinAt

omit [CompleteSpace F] in
/-- The actual smoothing integral is smooth on the output open domain
under regularity only on the open buffer containing its sampled points. -/
theorem signedSmoothing_contDiffOn {K : E → ℝ}
    (hK : ContDiff ℝ ∞ K) (hKcompact : HasCompactSupport K)
    {u : E → F} {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    (hu : ContDiffOn ℝ ∞ u V) (ell : ℝ)
    (hbuffer : ∀ x ∈ U, ∀ y ∈ tsupport K, x - ell • y ∈ V) :
    ContDiffOn ℝ ∞ (signedSmoothing mu K ell u) U := by
  apply contDiffOn_compactIntegral mu hU hKcompact
  · intro x hx y hy
    simp only [image_eq_zero_of_notMem_tsupport hy, zero_smul]
  · exact smoothingFamily_contDiffOn hK hV hu ell hbuffer

/-- Every native Fréchet derivative commutes with the actual smoothing
integral on the output domain. All source regularity is local to its
open buffer; in particular no global smooth extension is assumed. -/
theorem signedSmoothing_iteratedFDeriv_source_on {K : E → ℝ}
    (hK : ContDiff ℝ ∞ K) (hKcompact : HasCompactSupport K)
    {u : E → F} {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    (hu : ContDiffOn ℝ ∞ u V) (ell : ℝ)
    (hbuffer : ∀ x ∈ U, ∀ y ∈ tsupport K, x - ell • y ∈ V)
    (j : ℕ) {x : E} (hx : x ∈ U) :
    iteratedFDeriv ℝ j (signedSmoothing mu K ell u) x =
      ∫ y, K y • iteratedFDeriv ℝ j u (x - ell • y) ∂mu := by
  induction j generalizing x with
  | zero =>
    let e := (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv
    change e (∫ y, K y • u (x - ell • y) ∂mu) = _
    rw [← e.integral_comp_comm (fun y => K y • u (x - ell • y))]
    apply integral_congr_ae
    filter_upwards [] with y
    exact e.map_smul (K y) (u (x - ell • y))
  | succ j ih =>
    have hjet : ContDiffOn ℝ ∞ (iteratedFDeriv ℝ j u) V := by
      intro z hz
      exact ((hu.contDiffAt (hV.mem_nhds hz)).iteratedFDeriv_right (by simp)).contDiffWithinAt
    have heq : iteratedFDeriv ℝ j (signedSmoothing mu K ell u) =ᶠ[nhds x]
        signedSmoothing mu K ell (iteratedFDeriv ℝ j u) := by
      filter_upwards [hU.mem_nhds hx] with z hz
      exact ih hz
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, heq.fderiv_eq]
    have hd := hasFDerivAt_compactIntegral mu hU hKcompact
      (f := fun z y => K y • iteratedFDeriv ℝ j u (z - ell • y))
      (by
        intro z hz y hy
        simp only [image_eq_zero_of_notMem_tsupport hy, zero_smul])
      ((smoothingFamily_contDiffOn hK hV hjet ell hbuffer).of_le (by simp)) hx
    change HasFDerivAt (signedSmoothing mu K ell (iteratedFDeriv ℝ j u)) _ x at hd
    rw [hd.fderiv]
    let e : (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin j => E) F) ≃L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin (j + 1) => E) F :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) F).symm
        |>.toContinuousLinearEquiv
    change e (∫ y, fderiv ℝ (fun z => K y • iteratedFDeriv ℝ j u (z - ell • y)) x ∂mu) = _
    rw [← ContinuousLinearEquiv.integral_comp_comm (𝕜 := ℝ) (μ := mu) e
      (fun y : E => fderiv ℝ (fun z => K y • iteratedFDeriv ℝ j u (z - ell • y)) x)]
    apply integral_congr_ae
    filter_upwards [] with y
    change e (fderiv ℝ (K y • (fun z => iteratedFDeriv ℝ j u (z - ell • y))) x) = _
    rw [fderiv_const_smul_field (𝕜 := ℝ)
      (f := fun z => iteratedFDeriv ℝ j u (z - ell • y)) (K y)]
    change e (K y • fderiv ℝ (fun z => iteratedFDeriv ℝ j u (z - ell • y)) x) = _
    rw [fderiv_comp_sub, e.map_smul]
    rfl

end

end GlobalEmbedding.Offline
