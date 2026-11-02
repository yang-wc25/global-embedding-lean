import NormalPolar.OriginalMapGeometry

/-!
# An actual total family from data on the original probe domain

The original probe geometry has a total map and total normal isometries, but
the analytical construction only needs to give a family on its admitted
scale/parameter domain. Extend that actual family by the reference immersion
outside this domain. No point in the admitted domain, parameter radius or
scale threshold is changed. Equality on the original open parameter ball
transports every native parameter derivative, including mixed spatial jets.

In particular global slice immersion is a conclusion of the actual metric
identity, not an additional property demanded of an arbitrary outside map.
-/

noncomputable section
open Manifold Set Filter
open scoped ContDiff Topology

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade GlobalEmbedding.Offline

section Maps
variable {P X Y : Type*} [NormedAddCommGroup P]

/-- The explicit reference extension. Only the unprescribed outside values
are chosen; every admitted slice is the given actual slice as a function. -/
def actualFamilyTotalization (F₀ : X → Y) (F : ℝ → P → X → Y)
    (radius threshold : ℝ) (t : ℝ) (u : P) : X → Y :=
  if 0 < t ∧ t < threshold ∧ ‖u‖ < radius then F t u else F₀

theorem actualFamilyTotalization_eq (F₀ : X → Y) (F : ℝ → P → X → Y)
    (radius threshold : ℝ) (t : ℝ) (ht : 0 < t) (htt : t < threshold)
    (u : P) (hu : ‖u‖ < radius) :
    actualFamilyTotalization F₀ F radius threshold t u = F t u := by
  simp only [actualFamilyTotalization, ht, htt, hu, and_self, ite_true]

theorem actualFamilyTotalization_outside (F₀ : X → Y) (F : ℝ → P → X → Y)
    (radius threshold : ℝ) (t : ℝ) (u : P)
    (h : ¬ (0 < t ∧ t < threshold ∧ ‖u‖ < radius)) :
    actualFamilyTotalization F₀ F radius threshold t u = F₀ := by
  simp only [actualFamilyTotalization, ite_eq_right h]

/-- The whole actual slice, not just its value at one source point, agrees
throughout a parameter neighborhood. No regularity of an outside extension
is used. -/
theorem actualFamilyTotalization_eventuallyEq
    (F₀ : X → Y) (F : ℝ → P → X → Y) (radius threshold : ℝ)
    (t : ℝ) (ht : 0 < t) (htt : t < threshold) (u : P) (hu : ‖u‖ < radius) :
    actualFamilyTotalization F₀ F radius threshold t =ᶠ[𝓝 u] F t := by
  have hball : Metric.ball (0 : P) radius ∈ 𝓝 u :=
    Metric.isOpen_ball.mem_nhds (by simpa using hu)
  filter_upwards [hball] with v hv
  exact actualFamilyTotalization_eq F₀ F radius threshold t ht htt v (by simpa using hv)

end Maps

section ParameterDerivatives
variable {P X Y W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Apply any fixed operation to the same actual slice, then take the native
parameter derivative. The operation can be evaluation, an actual spatial
Hessian or any fixed-chart higher spatial jet; it need not be continuous. -/
theorem actualFamilyTotalization_fderiv_comp
    (F₀ : X → Y) (F : ℝ → P → X → Y) (radius threshold : ℝ)
    (t : ℝ) (ht : 0 < t) (htt : t < threshold) (u : P) (hu : ‖u‖ < radius)
    (op : (X → Y) → W) :
    fderiv ℝ (fun v ↦ op (actualFamilyTotalization F₀ F radius threshold t v)) u =
      fderiv ℝ (fun v ↦ op (F t v)) u := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [actualFamilyTotalization_eventuallyEq F₀ F radius threshold t ht htt u hu]
    with v hv
  rw [hv]

end ParameterDerivatives

section ParameterFields
variable {P X Y : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Equality as actual source fields allows every original atlas Cj norm of
the parameter response to be reused without a norm comparison or new loss. -/
theorem actualFamilyTotalization_parameterDerivative
    (F₀ : X → Y) (F : ℝ → P → X → Y) (radius threshold : ℝ)
    (t : ℝ) (ht : 0 < t) (htt : t < threshold) (u : P) (hu : ‖u‖ < radius) (d : P) :
    (fun x ↦ fderiv ℝ (fun v ↦ actualFamilyTotalization F₀ F radius threshold t v x) u d) =
      (fun x ↦ fderiv ℝ (fun v ↦ F t v x) u d) := by
  funext x
  exact congrArg (fun D : P →L[ℝ] Y ↦ D d)
    (actualFamilyTotalization_fderiv_comp F₀ F radius threshold t ht htt u hu (fun H ↦ H x))

end ParameterFields

variable {n N : ℕ} {M P : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ, E)

/-- Admitted slice smoothness follows from the supplied joint smoothness on
the original product domain. It is not a separate assumption. -/
theorem actualFamily_slice_smooth_of_joint
    (F : P → M → V) (radius : ℝ)
    (hjoint : ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V) ∞
      (Function.uncurry F) (Metric.ball 0 radius ×ˢ univ))
    (u : P) (hu : ‖u‖ < radius) : ContMDiff IM 𝓘(ℝ, V) ∞ (F u) := by
  exact hjoint.comp_contMDiff
    (contMDiff_const.prodMk contMDiff_id :
      ContMDiff IM ((𝓘(ℝ, P)).prod IM) ∞ (fun x : M ↦ (u, x)))
    (fun x ↦ ⟨by simpa using hu, mem_univ x⟩)

/-- Every total slice is genuinely smooth: use the joint family for an
admitted slice and the original reference elsewhere. -/
theorem actualFamilyTotalization_slice_smooth
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (F : ℝ → P → M → V) (radius threshold : ℝ)
    (hjoint : ∀ t, 0 < t → t < threshold →
      ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V) ∞
        (Function.uncurry (F t)) (Metric.ball 0 radius ×ˢ univ)) :
    ∀ t u, ContMDiff IM 𝓘(ℝ, V) ∞ (actualFamilyTotalization F₀ F radius threshold t u) := by
  intro t u
  by_cases h : 0 < t ∧ t < threshold ∧ ‖u‖ < radius
  · rw [actualFamilyTotalization_eq F₀ F radius threshold t h.1 h.2.1 u h.2.2]
    exact actualFamily_slice_smooth_of_joint (F t) radius (hjoint t h.1 h.2.1) u h.2.2
  · rw [actualFamilyTotalization_outside F₀ F radius threshold t u h]
    exact hF₀

/-- The original joint smoothness holds on exactly the same open ball and
scale interval. There is no claim of smoothness across its boundary. -/
theorem actualFamilyTotalization_joint_smooth
    (F₀ : M → V) (F : ℝ → P → M → V) (radius threshold : ℝ)
    (hjoint : ∀ t, 0 < t → t < threshold →
      ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V) ∞
        (Function.uncurry (F t)) (Metric.ball 0 radius ×ˢ univ))
    (t : ℝ) (ht : 0 < t) (htt : t < threshold) :
    ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V) ∞
      (Function.uncurry (actualFamilyTotalization F₀ F radius threshold t))
      (Metric.ball 0 radius ×ˢ univ) := by
  apply (hjoint t ht htt).congr
  intro z hz
  exact congrFun (actualFamilyTotalization_eq F₀ F radius threshold t ht htt z.1
    (by simpa using hz.1)) z.2

/-- The reference extension has the actual reference metric even outside
the domain. This is an equality of true induced metrics of actual maps. -/
theorem actualFamilyTotalization_metric
    (F₀ : M → V) (F : ℝ → P → M → V) (radius threshold : ℝ)
    (hmetric : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius → ∀ x,
      inducedMetric (I := IM) (F t u) x = inducedMetric (I := IM) F₀ x) :
    ∀ t u x, inducedMetric (I := IM) (actualFamilyTotalization F₀ F radius threshold t u) x =
      inducedMetric (I := IM) F₀ x := by
  intro t u x
  by_cases h : 0 < t ∧ t < threshold ∧ ‖u‖ < radius
  · rw [actualFamilyTotalization_eq F₀ F radius threshold t h.1 h.2.1 u h.2.2]
    exact hmetric t h.1 h.2.1 u h.2.2 x
  · rw [actualFamilyTotalization_outside F₀ F radius threshold t u h]

/-- Every actual total slice immerses. Only the actual metric on the
admitted domain and the reference immersion are required. -/
theorem actualFamilyTotalization_immersion
    (F₀ : M → V) (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (F : ℝ → P → M → V) (radius threshold : ℝ)
    (hmetric : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius → ∀ x,
      inducedMetric (I := IM) (F t u) x = inducedMetric (I := IM) F₀ x) :
    ∀ t u x, Function.Injective
      (mfderiv IM 𝓘(ℝ, V) (actualFamilyTotalization F₀ F radius threshold t u) x) := by
  intro t u x
  exact immersion_of_inducedMetric_eq F₀
    (actualFamilyTotalization F₀ F radius threshold t u) x
    (actualFamilyTotalization_metric F₀ F radius threshold hmetric t u x) (hi₀ x)

end GlobalEmbedding.NormalPolar
