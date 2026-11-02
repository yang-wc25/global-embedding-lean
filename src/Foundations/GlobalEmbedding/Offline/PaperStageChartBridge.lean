import GlobalEmbedding.Offline.CoordinateStageSeries
import GlobalEmbedding.Offline.ParametricMetricLimit

/-!
# Original stage norms, inner buffers and Euclidean target derivatives

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines 762–778.

The original `paperCoordinateCj` uses scalar components with the finite-product
sup norm. The actual induced metric uses `EuclideanSpace` with its Euclidean norm.
This file retains the genuine continuous linear equivalence between these spaces
and its fixed operator norm. Source model coordinates are likewise changed by an
explicit fixed continuous linear equivalence. No isometry between the two target
norms is assumed.

The original finite norm is evaluated on `S`, inside its open differentiation
domain `O`. Convergence is proved on an actual inner open buffer `U ⊆ S`. The
restriction and every derivative comparison are made explicit.
-/

open Set Filter Manifold GlobalEmbedding.Paper
open scoped Topology ContDiff ENNReal

namespace GlobalEmbedding.Offline

/-- Restrict the original componentwise norm from its actual norm domain to
an inner open buffer. Both differentiations are identified with the same actual
coordinate derivatives; arbitrary extensions outside the open domains do not
enter this comparison. -/
theorem paperCoordinateCj_restrict_buffer
    {n q : ℕ} (k : ℕ) {f : (Fin n → ℝ) → Fin q → ℝ}
    {O S U : Set (Fin n → ℝ)}
    (hO : IsOpen O) (hSO : S ⊆ O) (hU : IsOpen U) (hUS : U ⊆ S)
    (hf : ContDiffOn ℝ ∞ f O) :
    paperCoordinateCj k f U U ≤ paperCoordinateCj k f O S := by
  rw [paperCoordinateCj_eq_coordinateJetGauge k f U U hU (Subset.rfl)
      (hf.mono (hUS.trans hSO)),
    paperCoordinateCj_eq_coordinateJetGauge k f O S hO hSO hf]
  refine iSup_le fun a ↦ iSup_le fun x ↦ iSup_le fun σ ↦ iSup_le fun c ↦ ?_
  exact coordinate_jet_coefficient_le_gauge f S (by omega) ⟨x, hUS x.property⟩ σ c

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n q : ℕ}

/-- The actual scalar coordinate representative of a Euclidean-valued map.
The source equivalence is supplied explicitly; the target equivalence is the
canonical native Euclidean-to-finite-product map. -/
noncomputable def euclideanCoordinateRepresentative
    (e : E ≃L[ℝ] (Fin n → ℝ)) (u : E → EuclideanSpace ℝ (Fin q)) :
    (Fin n → ℝ) → Fin q → ℝ :=
  EuclideanSpace.equiv (Fin q) ℝ ∘ u ∘ e.symm

/-- Smoothness of the actual scalar representative gives smoothness of the
same Euclidean-valued map on the corresponding inner buffer. -/
theorem contDiffOn_of_euclideanCoordinateRepresentative
    (e : E ≃L[ℝ] (Fin n → ℝ)) (u : E → EuclideanSpace ℝ (Fin q))
    {O U : Set (Fin n → ℝ)} (hUO : U ⊆ O)
    (hu : ContDiffOn ℝ ∞ (euclideanCoordinateRepresentative e u) O) :
    ContDiffOn ℝ ∞ u (e ⁻¹' U) := by
  have heq : u = (EuclideanSpace.equiv (Fin q) ℝ).symm ∘
      (euclideanCoordinateRepresentative e u ∘ e) := by
    funext x
    simp [euclideanCoordinateRepresentative]
  rw [heq]
  exact (EuclideanSpace.equiv (Fin q) ℝ).symm.contDiff.comp_contDiffOn
    ((hu.mono hUO).comp_continuousLinearMap e.toContinuousLinearMap)

/-- The original finite coordinate norm bounds the true Euclidean-target
derivative on an inner buffer. The constants are the genuine target conversion
norm, the fixed observed-order factor `n^a`, and the actual source conversion
norm to the power `a`. They do not depend on the iteration stage or chart count. -/
theorem iteratedFDerivWithin_le_of_euclidean_coordinate_bound
    (e : E ≃L[ℝ] (Fin n → ℝ)) (u : E → EuclideanSpace ℝ (Fin q))
    {O S U : Set (Fin n → ℝ)}
    (hO : IsOpen O) (hSO : S ⊆ O) (hU : IsOpen U) (hUS : U ⊆ S)
    (hu : ContDiffOn ℝ ∞ (euclideanCoordinateRepresentative e u) O)
    {j a : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hbound : paperCoordinateCj j (euclideanCoordinateRepresentative e u) O S ≤
      ENNReal.ofReal B)
    (ha : a ≤ j) {x : E} (hx : e x ∈ U) :
    ‖iteratedFDerivWithin ℝ a u (e ⁻¹' U) x‖ ≤
      ‖(EuclideanSpace.equiv (Fin q) ℝ).symm.toContinuousLinearMap‖ *
        ((n : ℝ) ^ a * B) * ‖e.toContinuousLinearMap‖ ^ a := by
  let c := euclideanCoordinateRepresentative e u
  let L := (EuclideanSpace.equiv (Fin q) ℝ).symm
  have heq : u = L ∘ (c ∘ e) := by
    funext y
    simp [L, c, euclideanCoordinateRepresentative]
  have hV : IsOpen (e ⁻¹' U) := hU.preimage e.continuous
  have hc : ‖iteratedFDerivWithin ℝ a c U (e x)‖ ≤ (n : ℝ) ^ a * B := by
    rw [iteratedFDerivWithin_of_isOpen a hU hx]
    exact iteratedFDeriv_le_of_paperCoordinateCj_le hO hSO hu hB hbound ha (hUS hx)
  rw [heq, L.iteratedFDerivWithin_comp_left _ hV.uniqueDiffOn hx a,
    e.iteratedFDerivWithin_comp_right c hU.uniqueDiffOn hx a]
  have hsource := (iteratedFDerivWithin ℝ a c U (e x)).norm_compContinuousLinearMap_le
    (fun _ : Fin a ↦ e.toContinuousLinearMap)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hsource
  calc
    _ ≤ ‖L.toContinuousLinearMap‖ *
        ‖(iteratedFDerivWithin ℝ a c U (e x)).compContinuousLinearMap
          (fun _ : Fin a ↦ e.toContinuousLinearMap)‖ :=
      L.toContinuousLinearMap.norm_compContinuousMultilinearMap_le _
    _ ≤ ‖L.toContinuousLinearMap‖ *
        (‖iteratedFDerivWithin ℝ a c U (e x)‖ * ‖e.toContinuousLinearMap‖ ^ a) :=
      mul_le_mul_of_nonneg_left hsource (norm_nonneg _)
    _ ≤ ‖L.toContinuousLinearMap‖ * (((n : ℝ) ^ a * B) * ‖e.toContinuousLinearMap‖ ^ a) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hc (pow_nonneg (norm_nonneg _) _)) (norm_nonneg _)
    _ = _ := by dsimp [L]; ring

/-- Stage growth turns the original finite coordinate norm into an eventual
bound for every fixed true derivative. The dimension and coordinate conversion
factors depend only on the observed derivative order, not on `stage j`. -/
theorem eventually_native_derivative_bound_of_paper_stage_bound
    (e : E ≃L[ℝ] (Fin n → ℝ)) (u : ℕ → E → EuclideanSpace ℝ (Fin q))
    (stage : ℕ → ℕ) {O S U : Set (Fin n → ℝ)}
    (hO : IsOpen O) (hSO : S ⊆ O) (hU : IsOpen U) (hUS : U ⊆ S)
    (hu : ∀ j, ContDiffOn ℝ ∞ (euclideanCoordinateRepresentative e (u j)) O)
    (hstage : Tendsto stage atTop atTop)
    {t C : ℝ} (ht : 0 < t) (hC : 0 ≤ C)
    (hbound : ∀ j,
      paperCoordinateCj (stage j / 2) (euclideanCoordinateRepresentative e (u j)) O S ≤
        ENNReal.ofReal (C * iterationScale t j)) (a : ℕ) :
    ∀ᶠ j in atTop, ∀ x ∈ e ⁻¹' U,
      ‖iteratedFDerivWithin ℝ a (u j) (e ⁻¹' U) x‖ ≤
        (‖(EuclideanSpace.equiv (Fin q) ℝ).symm.toContinuousLinearMap‖ *
          (n : ℝ) ^ a * ‖e.toContinuousLinearMap‖ ^ a * C) * iterationScale t j := by
  have hlarge : ∀ᶠ j in atTop, 2 * a ≤ stage j :=
    hstage.eventually (eventually_ge_atTop (2 * a))
  filter_upwards [hlarge] with j hj x hx
  calc
    _ ≤ ‖(EuclideanSpace.equiv (Fin q) ℝ).symm.toContinuousLinearMap‖ *
        ((n : ℝ) ^ a * (C * iterationScale t j)) * ‖e.toContinuousLinearMap‖ ^ a :=
      iteratedFDerivWithin_le_of_euclidean_coordinate_bound e (u j) hO hSO hU hUS
        (hu j) (mul_nonneg hC (iterationScale_pos ht j).le) (hbound j) (by omega) hx
    _ = _ := by ring

variable {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- The actual paper stage bounds on finite norm domains imply exactly the
native buffered-coordinate hypotheses of `ChartSeriesLimit`. This theorem
performs both the inner-buffer restriction and the source/target norm conversion.
The displayed source equivalence is fixed for all iterations. -/
theorem native_chart_bounds_of_paper_stage_bounds
    (e : E ≃L[ℝ] (Fin n → ℝ)) (f : ℕ → M → EuclideanSpace ℝ (Fin q))
    (stage : ℕ → ℕ) (hstage : Tendsto stage atTop atTop) {t : ℝ} (ht : 0 < t)
    (hchart : ∀ x : M, ∃ O S U : Set (Fin n → ℝ),
      IsOpen O ∧ S ⊆ O ∧ IsOpen U ∧ U ⊆ S ∧ e (extChartAt I x x) ∈ U ∧
      (∀ j, ContDiffOn ℝ ∞
        (euclideanCoordinateRepresentative e (f j ∘ (extChartAt I x).symm)) O) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ j, paperCoordinateCj (stage j / 2)
        (euclideanCoordinateRepresentative e (f j ∘ (extChartAt I x).symm)) O S ≤
          ENNReal.ofReal (C * iterationScale t j))) :
    ∀ x : M, ∃ V : Set E,
      IsOpen V ∧ extChartAt I x x ∈ V ∧
      (∀ j, ContDiffOn ℝ ∞ (f j ∘ (extChartAt I x).symm) V) ∧
      (∀ a : ℕ, ∃ C : ℝ, ∃ K : ℕ, ∀ j ≥ K, ∀ y ∈ V,
        ‖iteratedFDerivWithin ℝ a (f j ∘ (extChartAt I x).symm) V y‖ ≤
          C * iterationScale t j) := by
  intro x
  obtain ⟨O, S, U, hO, hSO, hU, hUS, hx, hf, C, hC, hbound⟩ := hchart x
  refine ⟨e ⁻¹' U, hU.preimage e.continuous, hx, ?_, ?_⟩
  · intro j
    exact contDiffOn_of_euclideanCoordinateRepresentative e
      (f j ∘ (extChartAt I x).symm) (hUS.trans hSO) (hf j)
  · intro a
    obtain ⟨K, hK⟩ := eventually_atTop.mp
      (eventually_native_derivative_bound_of_paper_stage_bound e
        (fun j ↦ f j ∘ (extChartAt I x).symm) stage hO hSO hU hUS hf hstage ht hC hbound a)
    exact ⟨‖(EuclideanSpace.equiv (Fin q) ℝ).symm.toContinuousLinearMap‖ *
      (n : ℝ) ^ a * ‖e.toContinuousLinearMap‖ ^ a * C, K, hK⟩

/-- Original paper stage bounds, on their original finite norm domains, imply
the genuine smooth Euclidean-valued limit and its exact original induced metric.

Source: `thm:repair`, lines 762–776. This is the explicit end-to-end use of the
stage-to-tail theorem, the norm conversions, the actual chart derivative limit,
and the normalized-defect metric limit. It retains the geometric increment and
defect assumptions that the one-step construction must still supply. -/
theorem smooth_repair_series_metric_limit_of_paper_stage_bounds
    (e : E ≃L[ℝ] (Fin n → ℝ)) (F0 : M → EuclideanSpace ℝ (Fin q))
    (f : ℕ → M → EuclideanSpace ℝ (Fin q)) (stage : ℕ → ℕ)
    (delta : ℕ → ℝ)
    (g : ∀ x : M, LinearMap.BilinForm ℝ (TangentSpace I x))
    (Hseq : ℕ → ∀ x : M, LinearMap.BilinForm ℝ (TangentSpace I x))
    (hF0 : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) ∞ F0)
    (hstage : Tendsto stage atTop atTop) {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hchart : ∀ x : M, ∃ O S U : Set (Fin n → ℝ),
      IsOpen O ∧ S ⊆ O ∧ IsOpen U ∧ U ⊆ S ∧ e (extChartAt I x x) ∈ U ∧
      (∀ j, ContDiffOn ℝ ∞
        (euclideanCoordinateRepresentative e (f j ∘ (extChartAt I x).symm)) O) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ j, paperCoordinateCj (stage j / 2)
        (euclideanCoordinateRepresentative e (f j ∘ (extChartAt I x).symm)) O S ≤
          ENNReal.ofReal (C * iterationScale t j)))
    (hdelta : Tendsto delta atTop (𝓝 0))
    (hH : ∀ (x : M) (v w : TangentSpace I x),
      ∃ C : ℝ, ∀ᶠ j in atTop, ‖Hseq j x v w‖ ≤ C)
    (hdefect : ∀ j x, g x - GlobalEmbedding.Paper.inducedMetric (I := I)
      (fun y ↦ F0 y + ∑ i ∈ Finset.range j, f i y) x = delta j ^ 2 • Hseq j x) :
    (∀ x, Summable (fun j ↦ f j x)) ∧
    ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) ∞ (fun x ↦ F0 x + ∑' j, f j x) ∧
    GlobalEmbedding.Paper.inducedMetric (I := I) (fun x ↦ F0 x + ∑' j, f j x) = g :=
  smooth_repair_series_metric_limit F0 f (iterationScale t) delta g Hseq hF0
    (summable_iterationScale ht ht1)
    (native_chart_bounds_of_paper_stage_bounds e f stage hstage ht hchart)
    hdelta hH hdefect

variable {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  [TopologicalSpace HP] {J : ModelWithCorners ℝ EP HP}
  [TopologicalSpace P] [ChartedSpace HP P]

/-- The same original-norm bridge on product coordinates gives joint smoothness
and the exact SOURCE metric for every parameter. The fixed source coordinate
equivalence now acts on the whole product model; the metric conclusion still
uses only `TangentSpace I x`, as proved by `ParametricMetricLimit`. -/
theorem parametric_smooth_repair_series_metric_limit_of_paper_stage_bounds
    (e : (EP × E) ≃L[ℝ] (Fin n → ℝ))
    (F0 : P × M → EuclideanSpace ℝ (Fin q))
    (f : ℕ → P × M → EuclideanSpace ℝ (Fin q)) (stage : ℕ → ℕ)
    (delta : ℕ → ℝ)
    (g : P → ∀ x : M, LinearMap.BilinForm ℝ (TangentSpace I x))
    (Hseq : ℕ → P → ∀ x : M, LinearMap.BilinForm ℝ (TangentSpace I x))
    (hF0 : ContMDiff (J.prod I) 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) ∞ F0)
    (hstage : Tendsto stage atTop atTop) {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hchart : ∀ z : P × M, ∃ O S U : Set (Fin n → ℝ),
      IsOpen O ∧ S ⊆ O ∧ IsOpen U ∧ U ⊆ S ∧ e (extChartAt (J.prod I) z z) ∈ U ∧
      (∀ j, ContDiffOn ℝ ∞
        (euclideanCoordinateRepresentative e (f j ∘ (extChartAt (J.prod I) z).symm)) O) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ j, paperCoordinateCj (stage j / 2)
        (euclideanCoordinateRepresentative e (f j ∘ (extChartAt (J.prod I) z).symm)) O S ≤
          ENNReal.ofReal (C * iterationScale t j)))
    (hdelta : Tendsto delta atTop (𝓝 0))
    (hH : ∀ (p : P) (x : M) (v w : TangentSpace I x),
      ∃ C : ℝ, ∀ᶠ j in atTop, ‖Hseq j p x v w‖ ≤ C)
    (hdefect : ∀ j p x, g p x - GlobalEmbedding.Paper.inducedMetric (I := I)
      (fun y ↦ F0 (p, y) + ∑ i ∈ Finset.range j, f i (p, y)) x =
        delta j ^ 2 • Hseq j p x) :
    (∀ z, Summable (fun j ↦ f j z)) ∧
    ContMDiff (J.prod I) 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) ∞
      (fun z ↦ F0 z + ∑' j, f j z) ∧
    (∀ p, ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) ∞
        (fun x ↦ F0 (p, x) + ∑' j, f j (p, x)) ∧
      GlobalEmbedding.Paper.inducedMetric (I := I)
        (fun x ↦ F0 (p, x) + ∑' j, f j (p, x)) = g p) :=
  parametric_smooth_repair_series_metric_limit F0 f (iterationScale t) delta g Hseq hF0
    (summable_iterationScale ht ht1)
    (native_chart_bounds_of_paper_stage_bounds e f stage hstage ht hchart)
    hdelta hH hdefect

#print axioms paperCoordinateCj_restrict_buffer
#print axioms contDiffOn_of_euclideanCoordinateRepresentative
#print axioms iteratedFDerivWithin_le_of_euclidean_coordinate_bound
#print axioms eventually_native_derivative_bound_of_paper_stage_bound
#print axioms native_chart_bounds_of_paper_stage_bounds
#print axioms smooth_repair_series_metric_limit_of_paper_stage_bounds
#print axioms parametric_smooth_repair_series_metric_limit_of_paper_stage_bounds

end GlobalEmbedding.Offline
