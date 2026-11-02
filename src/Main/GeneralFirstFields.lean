import Main.GeneralActualProbeFirstModelBounds
import ProbesClosure.GeneralFourFields

/-!
# The six first-model fields from independent actual-map bounds

The grouped original construction supplies its spatial bounds from its own
weighted increment budget and its parameter fields from the same complete
first map. They meet here without an artificial conversion to the older
single-chart prescribed raw-slice record.

This is only record assembly: every input bound is explicit, and every
output field refers to the same G, atlas, original wave family, parameter
radius and threshold. One maximum pays the shared constant. Neither the
map nor the weights nor the two error moduli are changed.
-/

noncomputable section
open Set Function Filter Manifold GlobalEmbedding.Paper
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar GlobalEmbedding.Upgrade

variable {n N r : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,E)

/-- Assemble the actual two spatial and four parameter fields. Unlike the
older raw-slice adapter, this constructor is also applicable when the
prescribed wave consists of several pieces under each original label. -/
def general_probes_first_model_of_spatial_and_four
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ,V) ∞ F₀)
    (A : BufferedAtlas M E) (waves : Fin r → OpenSupportedLegalWave F₀ hF₀)
    (G : ℝ → ProbeParameters r → M → V) (radius threshold : ℝ)
    (weight : Fin r → ℝ) (hweight : ∀ l, 0 < weight l)
    (hdistinct : ∀ l k, l ≠ k →
      (tsupport (waves l).cutoff ∩ tsupport (waves k).cutoff).Nonempty → weight l ≠ weight k)
    (Cspatial Cparam : ℝ) (hCspatial : 0 ≤ Cspatial)
    (etaH etaV : ℝ → ℝ)
    (hHnon : ∀ t, 0 ≤ etaH t) (hVnon : ∀ t, 0 ≤ etaV t)
    (hHlim : Tendsto etaH (𝓝[>] 0) (𝓝 0))
    (hVlim : Tendsto etaV (𝓝[>] 0) (𝓝 0))
    (spatial : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius →
      probeAtlasCj A 2 (G t u-F₀) ≤ ENNReal.ofReal (Cspatial*t^((44:ℝ)/5)) ∧
      probeAtlasCj A 3 (G t u) ≤ ENNReal.ofReal Cspatial)
    (four : ∀ t, 0 < t → t < threshold →
      GeneralWaveFirstFourAt F₀ hF₀ waves A weight (G t)
        (Metric.ball 0 radius) radius t Cparam (etaH t) (etaV t)) :
    GeneralActualProbeFirstModelBounds F₀ hF₀ A waves G radius threshold := by
  let C := max Cspatial Cparam
  have hCs : Cspatial ≤ C := le_max_left _ _
  have hCp : Cparam ≤ C := le_max_right _ _
  have hf (t : ℝ) (ht : 0 < t) (htt : t < threshold)
      (u : ProbeParameters r) (hu : ‖u‖ < radius) :=
    four t ht htt u
      (show u ∈ Metric.ball 0 radius by
        simpa only [Metric.mem_ball,dist_zero_right] using hu) hu
  refine {
    weight := weight
    weight_pos := hweight
    distinct_on_overlap := hdistinct
    constant := C
    constant_nonneg := hCspatial.trans hCs
    etaH := etaH
    etaV := etaV
    etaH_nonneg := hHnon
    etaV_nonneg := hVnon
    etaH_tendsto := hHlim
    etaV_tendsto := hVlim
    closeness := ?_
    spatial_C3 := ?_
    parameter_C1 := ?_
    parameter_C2 := ?_
    hessian_response := ?_
    value_response := ?_ }
  · intro t ht htt u hu
    exact (spatial t ht htt u hu).1.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hCs (Real.rpow_nonneg ht.le _)))
  · intro t ht htt u hu
    exact (spatial t ht htt u hu).2.trans (ENNReal.ofReal_le_ofReal hCs)
  · intro t ht htt u hu direction
    exact ((hf t ht htt u hu).1 direction).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCp (pow_nonneg ht.le _)) (norm_nonneg _)))
  · intro t ht htt u hu direction
    exact ((hf t ht htt u hu).2.1 direction).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCp (Real.rpow_nonneg ht.le _)) (norm_nonneg _)))
  · intro t ht htt u hu l sine i x hx
    exact ((hf t ht htt u hu).2.2.1 l sine i x hx).trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (mul_le_mul_of_nonneg_right hCp (norm_nonneg _))) (Real.rpow_nonneg ht.le _))
  · intro t ht htt u hu l sine x
    exact ((hf t ht htt u hu).2.2.2 l sine x).trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (mul_le_mul_of_nonneg_right hCp (norm_nonneg _))) (Real.rpow_nonneg ht.le _))

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.general_probes_first_model_of_spatial_and_four
