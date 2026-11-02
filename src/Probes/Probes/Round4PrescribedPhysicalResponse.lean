import Probes.Round4PrescribedPhysicalResidual
import Probes.ActualSecondaryConstructedCancellation

/-!
# Native probe-parameter derivatives of the physical first-mode residual

The finite source superposition is transported through the actual spatial
derivative and metric linearization.  Thus the parameter derivative below is
the derivative of the real residual, not an independently supplied error field.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {m N p r : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Cdata" => Fin (m+1) → ℂ

/-- Real source superposition survives the complete prescribed mode. -/
theorem round4ActualProbeMode_finite_source
    (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ,V) ∞ F) (c : D → M)
    (vf : (x : D) → normalSpace (I := I) F (c x))
    (phi : D → ℝ) (tau : ℝ) (length : ℕ)
    (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF c) O)
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF c) O)
    (hs : ContDiffOn ℝ ∞ (fun x => incrementsModeComplexInclude
      (incrementsModeSource F hF c (fun _ _ _ => 0) vf x)) O)
    (u : Fin p → ℝ) (x : D) (hx : x ∈ O) :
    round4ActualProbeMode label l F hF c vf phi tau length u x =
      finiteProbeSource (fun q => round4ActualProbeMode label l F hF c vf phi tau length
        (Pi.single q 1)) u x := by
  classical
  let source := fun x => incrementsModeComplexInclude
    (incrementsModeSource F hF c (fun _ _ _ => 0) vf x)
  let k := pairedProbeSourceDictionary label l source
  have hk (q : Fin p) : ContDiffOn ℝ ∞ (k q) O :=
    pairedProbeSourceDictionary_contDiffOn label l source O hs q
  have hcol (q : Fin p) : actualPairedNormalSource label l F hF c vf (Pi.single q 1) = k q := by
    rw [actualPairedNormalSource_eq_finite_source]
    funext y
    simp [finiteProbeSource,k,source,Pi.single_apply]
  have hr := actualRealHomogeneousProbe_finite_source phi F hF c tau length k O hO
    hA hB hk x hx u
  have hsource : actualPairedNormalSource label l F hF c vf u = finiteProbeSource k u :=
    actualPairedNormalSource_eq_finite_source label l F hF c vf u
  simp only [round4ActualProbeMode,hsource,hcol,hr,finiteProbeSource,
    smul_add,smul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  congr 1
  simp [Pi.single_apply,smul_smul,smul_neg,neg_smul,mul_comm]

section Linearization
variable {Ep Es Y ι : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Es] [NormedSpace ℝ Es]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [Fintype ι]

private local instance responseTensorSemi : SeminormedAddCommGroup (Es →L[ℝ] Es →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance responseTensorNormed : NormedAddCommGroup (Es →L[ℝ] Es →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance responseTensorSpace : NormedSpace ℝ (Es →L[ℝ] Es →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Linearity of the genuine metric first variation on the actual finite
source family, with spatial differentiability checked before distribution. -/
theorem round4_metric_linearization_finite_source
    (F : Ep → Es → Y) (g : ι → Ep × Es → Y)
    (W : (ι → ℝ) → Ep × Es → Y) (O : Set (Ep × Es)) (hO : IsOpen O)
    (hg : ∀ q, ContDiffOn ℝ ∞ (g q) O)
    (hW : ∀ u z, z ∈ O → W u z = finiteProbeSource g u z)
    (u : ι → ℝ) (z : Ep × Es) (hz : z ∈ O) :
    actualCoordinateMetricLinearization (F z.1) (fun x => W u (z.1,x)) z.2 =
      finiteProbeSource (fun q (w : Ep × Es) =>
        actualCoordinateMetricLinearization (F w.1) (fun x => g q (w.1,x)) w.2) u z := by
  have hslice : IsOpen ((fun x : Es => (z.1,x)) ⁻¹' O) :=
    hO.preimage (continuous_const.prodMk continuous_id)
  have he : (fun x => W u (z.1,x)) =ᶠ[𝓝 z.2]
      (fun x => finiteProbeSource g u (z.1,x)) :=
    eventuallyEq_of_mem (hslice.mem_nhds hz) (fun x hx => hW u (z.1,x) hx)
  have hc (q : ι) : DifferentiableAt ℝ (fun x : Es => g q (z.1,x)) z.2 :=
    (((hg q).comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun _ hx => hx)).contDiffAt (hslice.mem_nhds hz)).differentiableAt (by simp)
  have hsum : fderiv ℝ (fun x => finiteProbeSource g u (z.1,x)) z.2 =
      ∑ q, u q • fderiv ℝ (fun x => g q (z.1,x)) z.2 := by
    unfold finiteProbeSource
    rw [fderiv_fun_sum (u := Finset.univ)
      (A := fun q x => u q • g q (z.1,x)) (fun q _ => (hc q).const_smul (u q))]
    simp only [fderiv_fun_const_smul (hc _)]
  ext v w
  simp only [actualCoordinateMetricLinearization_apply,he.fderiv_eq]
  rw [hsum]
  simp only [finiteProbeSource,sum_apply,smul_apply,
    inner_sum, sum_inner, inner_smul_right, inner_smul_left,starRingEnd_apply,
    star_trivial,smul_eq_mul,actualCoordinateMetricLinearization_apply,
    mul_add,Finset.sum_add_distrib]

/-- Actual parameter differentiation after each full auxiliary/spatial jet of
the actual physical residual. Its operator norm uses the bound for all real
parameter vectors; there is no factor equal to the parameter dimension. -/
theorem round4_metric_linearization_parameter_jet_bound
    (F : Ep → Es → Y) (g : ι → Ep × Es → Y)
    (W : (ι → ℝ) → Ep × Es → Y) (O : Set (Ep × Es)) (hO : IsOpen O)
    (hg : ∀ q, ContDiffOn ℝ ∞ (g q) O)
    (hW : ∀ u z, z ∈ O → W u z = finiteProbeSource g u z)
    (hE : ∀ q, ContDiffOn ℝ ∞ (fun w : Ep × Es =>
      actualCoordinateMetricLinearization (F w.1) (fun x => g q (w.1,x)) w.2) O)
    (j : ℕ) (z : Ep × Es) (hz : z ∈ O) (tau C : ℝ) (htau : 0 ≤ tau) (hC : 0 ≤ C)
    (hb : ∀ u, tau^j * ‖iteratedFDeriv ℝ j (fun w : Ep × Es =>
      actualCoordinateMetricLinearization (F w.1) (fun x => W u (w.1,x)) w.2) z‖ ≤ C*‖u‖)
    (u : ι → ℝ) :
    tau^j * ‖fderiv ℝ (fun v : ι → ℝ => iteratedFDeriv ℝ j (fun w : Ep × Es =>
      actualCoordinateMetricLinearization (F w.1) (fun x => W v (w.1,x)) w.2) z) u‖ ≤ C := by
  let cols := fun q (w : Ep × Es) =>
    actualCoordinateMetricLinearization (F w.1) (fun x => g q (w.1,x)) w.2
  let L := probeColumnMap (fun q => iteratedFDeriv ℝ j (cols q) z)
  have hjet (v : ι → ℝ) :
      iteratedFDeriv ℝ j (fun w : Ep × Es =>
        actualCoordinateMetricLinearization (F w.1) (fun x => W v (w.1,x)) w.2) z = L v := by
    have he : (fun w : Ep × Es => actualCoordinateMetricLinearization
        (F w.1) (fun x => W v (w.1,x)) w.2) =ᶠ[𝓝 z] finiteProbeSource cols v :=
      eventuallyEq_of_mem (hO.mem_nhds hz) (fun w hw =>
        round4_metric_linearization_finite_source F g W O hO hg hW v w hw)
    rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]
    exact iteratedFDeriv_finiteProbeSource cols v j z
      (fun q => ((hE q).contDiffAt (hO.mem_nhds hz)).of_le (by simp))
  rw [show (fun v : ι → ℝ => iteratedFDeriv ℝ j (fun w : Ep × Es =>
      actualCoordinateMetricLinearization (F w.1) (fun x => W v (w.1,x)) w.2) z) = L
    from funext hjet,L.fderiv]
  have hb' : ‖(tau^j) • L‖ ≤ C := by
    apply ContinuousLinearMap.opNorm_le_bound _ hC
    intro v
    simpa only [smul_apply,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg htau j),hjet v] using hb v
  simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg htau j)] using hb'

end Linearization
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.round4ActualProbeMode_finite_source
#print axioms GlobalEmbedding.Continuation.round4_metric_linearization_finite_source
#print axioms GlobalEmbedding.Continuation.round4_metric_linearization_parameter_jet_bound
