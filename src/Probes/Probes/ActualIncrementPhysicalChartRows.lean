import Probes.ActualIncrementChartGeometry
import GlobalEmbedding.Paper.IncrementsModeRowResidual

/-!
# Physical metric rows in the actual chosen maximal chart

The canonical extChartAt restriction in the older physical-row interface is
removed by proving the chart transport for the arbitrary maximal chart used
by the construction. All original reconstruction, source, true-B, Gamma,
phase and 11/mixed/transverse row expressions are retained literally.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Filter
open scoped Topology ContDiff
namespace GlobalEmbedding.Continuation

section ActualChart

variable {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ, D)
local notation "Cdata" => Fin (m + 1) → ℂ

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) M]

/-- Injectivity of the actual manifold derivative transfers through the SAME
chosen maximal chart, using its genuine inverse differential. -/
theorem actual_increment_chart_derivative_injective
    (F : M → V) (hF : ContMDiff 𝓙 𝓘(ℝ, V) ∞ F)
    (chart : OpenPartialHomeomorph M D) (heChart : chart ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (x : D) (hx : x ∈ chart.target)
    (hinj : Function.Injective (mfderiv 𝓙 𝓘(ℝ, V) F (chart.symm x))) :
    Function.Injective (fderiv ℝ (F ∘ chart.symm) x) := by
  have ha1 : chart ∈ IsManifold.maximalAtlas 𝓙 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) heChart
  have hac : chart.MDifferentiable 𝓙 𝓙 := by
    constructor
    · intro q hq
      exact (mdifferentiableAt_of_mem_maximalAtlas ha1 hq).mdifferentiableWithinAt
    · intro q hq
      exact (mdifferentiableAt_symm_of_mem_maximalAtlas ha1 hq).mdifferentiableWithinAt
  have hpush : fderiv ℝ (F ∘ chart.symm) x =
      ((tangentSpaceCastModel 𝓘(ℝ, V) (F (chart.symm x))).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓘(ℝ, V) F (chart.symm x))).comp
          (mfderiv 𝓙 𝓙 chart.symm x) := by
    have hc := hac.mdifferentiableAt_symm hx
    have h := mfderiv_comp x (hF.mdifferentiable (by simp) _) hc
    rw [mfderiv_eq_fderiv] at h
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun L ↦ tangentSpaceCastModel 𝓘(ℝ, V) (F (chart.symm x))
      (L ((tangentSpaceCastModel 𝓙 x).symm v))) h
  rw [hpush]
  exact ((tangentSpaceCastModel 𝓘(ℝ, V) (F (chart.symm x))).injective.comp hinj).comp
    (hac.symm.mfderiv hx).injective

/-- The accepted literal metric conjugation, in the SAME original inverse chart,
uses exactly the canonical true B and Gamma of the row identities above. The
adapted phase is the actual first coordinate, so its phase term is the true delta
term. This only transports accepted geometric identities; no new reconstruction,
normal inverse, metric or differential-solver definition is introduced. -/
theorem actual_increment_physical_metric_row
    (F : M → V) (hF : ContMDiff 𝓙 𝓘(ℝ, V) ∞ F) (chart : OpenPartialHomeomorph M D)
    (heChart : chart ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (Ω : Set D) (hΩ : IsOpen Ω) (hΩt : Ω ⊆ chart.target)
    (hinj : ∀ z ∈ Ω, Function.Injective
      (mfderiv 𝓙 𝓘(ℝ, V) F (chart.symm z)))
    (u : D → Cdata)
    (νR νI : (z : D) → normalSpace (I := 𝓙) F (chart.symm z))
    (τ : ℝ) (x : D) (hx : x ∈ Ω) (hu : DifferentiableAt ℝ u x)
    (hνR : DifferentiableAt ℝ (fun z ↦ (νR z : V)) x)
    (hνI : DifferentiableAt ℝ (fun z ↦ (νI z : V)) x) (i j : Fin (m + 1)) :
    let c := chart.symm
    let uR := fun z ↦ incrementsModeRealPart (u z)
    let uI := fun z ↦ incrementsModeImagPart (u z)
    let P := fun z ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) z) (uR z) + (νR z : V)
    let Q := fun z ↦ freeGramRightInverse (fderiv ℝ (F ∘ c) z) (uI z) + (νI z : V)
    let R := fun z ↦ WithLp.toLp 2 (fun a : Fin N ↦
      (Complex.exp (((z 0 / τ : ℝ) : ℂ) * Complex.I) *
        ((P z a : ℂ) + Complex.I * (Q z a : ℂ))).re)
    let S := fun z ↦ WithLp.toLp 2 (fun a : Fin N ↦
      (Complex.exp (((z 0 / τ : ℝ) : ℂ) * Complex.I) *
        ((P z a : ℂ) + Complex.I * (Q z a : ℂ))).im)
    Complex.exp (-((x 0 / τ : ℝ) : ℂ) * Complex.I) *
        ((incrementsCoordinateMetricVariation (F ∘ c) R x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) : ℂ) +
          Complex.I * (incrementsCoordinateMetricVariation (F ∘ c) S x
            (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) : ℂ)) =
      ((fderiv ℝ uR x (EuclideanSpace.single i 1)) j +
        (fderiv ℝ uR x (EuclideanSpace.single j 1)) i -
        2 * inner ℝ (incrementsModeGamma F c x i j) (uR x) -
        2 * inner ℝ (incrementsModeSecondForm F hF c x i j) (νR x) : ℝ) +
      Complex.I * ((fderiv ℝ uI x (EuclideanSpace.single i 1)) j +
        (fderiv ℝ uI x (EuclideanSpace.single j 1)) i -
        2 * inner ℝ (incrementsModeGamma F c x i j) (uI x) -
        2 * inner ℝ (incrementsModeSecondForm F hF c x i j) (νI x) : ℝ) +
      (Complex.I / (τ : ℂ)) *
        ((if i = 0 then u x j else 0) + (if j = 0 then u x i else 0)) := by
  let c := chart.symm
  let uR := fun z ↦ incrementsModeRealPart (u z)
  let uI := fun z ↦ incrementsModeImagPart (u z)
  have hFc : ContDiffOn ℝ ∞ (F ∘ c) Ω :=
    ((hF.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas heChart)).contDiffOn).mono hΩt
  have hcInj : ∀ z ∈ Ω, Function.Injective (fderiv ℝ (F ∘ c) z) := by
    intro z hz
    exact actual_increment_chart_derivative_injective F hF chart heChart z (hΩt hz) (hinj z hz)
  have hnR : ∀ z ∈ Ω,
      (νR z : V) ∈ (LinearMap.range (fderiv ℝ (F ∘ c) z).toLinearMap)ᗮ := by
    intro z hz
    rw [← actual_increment_normalSpace_eq_chart_range F hF chart heChart z (hΩt hz)]
    exact (νR z).property
  have hnI : ∀ z ∈ Ω,
      (νI z : V) ∈ (LinearMap.range (fderiv ℝ (F ∘ c) z).toLinearMap)ᗮ := by
    intro z hz
    rw [← actual_increment_normalSpace_eq_chart_range F hF chart heChart z (hΩt hz)]
    exact (νI z).property
  have huR : DifferentiableAt ℝ uR x := incrementsModeRealPart.differentiableAt.comp x hu
  have huI : DifferentiableAt ℝ uI x := incrementsModeImagPart.differentiableAt.comp x hu
  have hψ : DifferentiableAt ℝ (fun z : D ↦ z 0) x :=
    (EuclideanSpace.proj (0 : Fin (m + 1)) : D →L[ℝ] ℝ).differentiableAt
  have hd (a : Fin (m + 1)) :
      fderiv ℝ (fun z : D ↦ z 0) x (EuclideanSpace.single a 1) =
        if a = 0 then 1 else 0 := by
    have hproj : fderiv ℝ (fun z : D ↦ z 0) x =
        (EuclideanSpace.proj (0 : Fin (m + 1)) : D →L[ℝ] ℝ) :=
      (EuclideanSpace.proj (0 : Fin (m + 1)) : D →L[ℝ] ℝ).hasFDerivAt.fderiv
    rw [hproj]
    simp [EuclideanSpace.proj, PiLp.single_apply, eq_comm]
  have hp (a : Fin (m + 1)) : (uR x a : ℂ) + Complex.I * (uI x a : ℂ) = u x a := by
    change ((u x a).re : ℂ) + Complex.I * ((u x a).im : ℂ) = u x a
    simpa only [mul_comm] using Complex.re_add_im (u x a)
  have hb := actual_increment_secondForm_chart F hF chart heChart x (hΩt hx) i j
  conv_rhs at hb =>
    rw [actual_increment_normalSpace_eq_chart_range F hF chart heChart x (hΩt hx)]
  have hm := increments_complex_linearized_metric Ω hΩ (F ∘ c) hFc hcInj uR uI
    (fun z ↦ (νR z : V)) (fun z ↦ (νI z : V)) hnR hnI (fun z ↦ z 0) τ x hx
    huR huI hνR hνI hψ (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  dsimp only at hm
  rw [← hb] at hm
  simp only [EuclideanSpace.inner_single_right, conj_trivial, one_mul] at hm
  rw [hp j, hp i, hd i, hd j] at hm
  refine hm.trans ?_
  dsimp only [uR, uI, c, incrementsModeGamma]
  simp only [Submodule.coe_inner]
  split_ifs <;> push_cast <;> ring


/-- ORIGINAL actual physical metric errors of the SAME normal reconstruction are
2e in row11, e in mixed rows, and zero in every once-sorted transverse row. Here e
is the literal reduced expression, not a supplied PDE or output identity. Only
actual differentiability of the reconstructed normal fields is an upstream
regularity input. No R/J construction or geometric estimate is duplicated. -/
theorem actual_increment_physical_residual_rows
    (F : M → V) (hF : ContMDiff 𝓙 𝓘(ℝ, V) ∞ F) (chart : OpenPartialHomeomorph M D)
    (heChart : chart ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (Ω : Set D) (hΩ : IsOpen Ω) (hΩt : Ω ⊆ chart.target)
    (hinj : ∀ z ∈ Ω, Function.Injective
      (mfderiv 𝓙 𝓘(ℝ, V) F (chart.symm z)))
    (u : D → Cdata) (hR hI : D → Fin (m + 1) → Fin (m + 1) → ℝ)
    (vfR vfI : (z : D) → normalSpace (I := 𝓙) F (chart.symm z))
    (τ : ℝ) (x : D) (hx : x ∈ Ω) (hu : DifferentiableAt ℝ u x)
    (hG : ((incrementsTransversePairing F hF (chart.symm x)
      (fun a ↦ incrementsModeCoordinateDirections chart.symm x a.succ)).comp
      (incrementsTransversePairing F hF (chart.symm x)
        (fun a ↦
          incrementsModeCoordinateDirections chart.symm x a.succ)).adjoint).IsInvertible)
    (hfreeR : incrementsTransversePairing F hF (chart.symm x)
      (fun a ↦ incrementsModeCoordinateDirections chart.symm x a.succ)
      (vfR x) = 0)
    (hfreeI : incrementsTransversePairing F hF (chart.symm x)
      (fun a ↦ incrementsModeCoordinateDirections chart.symm x a.succ)
      (vfI x) = 0) :
    let c := chart.symm
    let uR := fun z ↦ incrementsModeRealPart (u z)
    let uI := fun z ↦ incrementsModeImagPart (u z)
    let νR := fun z ↦ vfR z + incrementsModeCoordinateJ F hF c z
      (incrementsModeTransverseTensor F c uR z) - (1 / 2 : ℝ) •
      incrementsModeCoordinateJ F hF c z (incrementsModeTransverseSource hR z)
    let νI := fun z ↦ vfI z + incrementsModeCoordinateJ F hF c z
      (incrementsModeTransverseTensor F c uI z) - (1 / 2 : ℝ) •
      incrementsModeCoordinateJ F hF c z (incrementsModeTransverseSource hI z)
    DifferentiableAt ℝ (fun z ↦ (νR z : V)) x →
    DifferentiableAt ℝ (fun z ↦ (νI z : V)) x →
    let ZR := incrementsModeFullReconstruction F hF c uR hR vfR
    let ZI := incrementsModeFullReconstruction F hF c uI hI vfI
    let WR := fun z ↦ WithLp.toLp 2 (fun a : Fin N ↦
      (Complex.exp (((z 0 / τ : ℝ) : ℂ) * Complex.I) *
        ((ZR z a : ℂ) + Complex.I * (ZI z a : ℂ))).re)
    let WI := fun z ↦ WithLp.toLp 2 (fun a : Fin N ↦
      (Complex.exp (((z 0 / τ : ℝ) : ℂ) * Complex.I) *
        ((ZR z a : ℂ) + Complex.I * (ZI z a : ℂ))).im)
    let err := fun i j ↦ Complex.exp (-((x 0 / τ : ℝ) : ℂ) * Complex.I) *
      ((incrementsCoordinateMetricVariation (F ∘ c) WR x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) : ℂ) +
        Complex.I * (incrementsCoordinateMetricVariation (F ∘ c) WI x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) : ℂ)) -
      ((hR x i j : ℂ) + Complex.I * (hI x i j : ℂ))
    let k := incrementsModeComplexInclude (incrementsModeSource F hF c hR vfR x) +
      Complex.I • incrementsModeComplexInclude (incrementsModeSource F hF c hI vfI x)
    let e := (((τ : ℂ) / Complex.I)⁻¹ • u x) +
      incrementsModeComplexReducedOperator F hF c u x - k
    err 0 0 = 2 * e 0 ∧ (∀ a : Fin m, err 0 a.succ = e a.succ) ∧
      ∀ q : {p : Fin m × Fin m // p.1 ≤ p.2}, err q.val.1.succ q.val.2.succ = 0 := by
  dsimp only
  let c := chart.symm
  let uR := fun z ↦ incrementsModeRealPart (u z)
  let uI := fun z ↦ incrementsModeImagPart (u z)
  let νR := fun z ↦ vfR z + incrementsModeCoordinateJ F hF c z
      (incrementsModeTransverseTensor F c uR z) - (1 / 2 : ℝ) •
      incrementsModeCoordinateJ F hF c z (incrementsModeTransverseSource hR z)
  let νI := fun z ↦ vfI z + incrementsModeCoordinateJ F hF c z
      (incrementsModeTransverseTensor F c uI z) - (1 / 2 : ℝ) •
      incrementsModeCoordinateJ F hF c z (incrementsModeTransverseSource hI z)
  intro hνR hνI
  let ZR := incrementsModeFullReconstruction F hF c uR hR vfR
  let ZI := incrementsModeFullReconstruction F hF c uI hI vfI
  let WR := fun z ↦ WithLp.toLp 2 (fun a : Fin N ↦
    (Complex.exp (((z 0 / τ : ℝ) : ℂ) * Complex.I) *
      ((ZR z a : ℂ) + Complex.I * (ZI z a : ℂ))).re)
  let WI := fun z ↦ WithLp.toLp 2 (fun a : Fin N ↦
    (Complex.exp (((z 0 / τ : ℝ) : ℂ) * Complex.I) *
      ((ZR z a : ℂ) + Complex.I * (ZI z a : ℂ))).im)
  let err := fun i j ↦ Complex.exp (-((x 0 / τ : ℝ) : ℂ) * Complex.I) *
    ((incrementsCoordinateMetricVariation (F ∘ c) WR x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) : ℂ) +
      Complex.I * (incrementsCoordinateMetricVariation (F ∘ c) WI x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) : ℂ)) -
    ((hR x i j : ℂ) + Complex.I * (hI x i j : ℂ))
  let k := incrementsModeComplexInclude (incrementsModeSource F hF c hR vfR x) +
    Complex.I • incrementsModeComplexInclude (incrementsModeSource F hF c hI vfI x)
  let e := (((τ : ℂ) / Complex.I)⁻¹ • u x) +
    incrementsModeComplexReducedOperator F hF c u x - k
  let α := (τ : ℂ) / Complex.I
  let rowR := fun i j ↦ (fderiv ℝ uR x (EuclideanSpace.single i 1)) j +
    (fderiv ℝ uR x (EuclideanSpace.single j 1)) i -
    2 * inner ℝ (incrementsModeGamma F c x i j) (uR x) -
    2 * inner ℝ (incrementsModeSecondForm F hF c x i j) (νR x) - hR x i j
  let rowI := fun i j ↦ (fderiv ℝ uI x (EuclideanSpace.single i 1)) j +
    (fderiv ℝ uI x (EuclideanSpace.single j 1)) i -
    2 * inner ℝ (incrementsModeGamma F c x i j) (uI x) -
    2 * inner ℝ (incrementsModeSecondForm F hF c x i j) (νI x) - hI x i j
  change err 0 0 = 2 * e 0 ∧ (∀ a : Fin m, err 0 a.succ = e a.succ) ∧
    ∀ q : {p : Fin m × Fin m // p.1 ≤ p.2}, err q.val.1.succ q.val.2.succ = 0
  have hphys (i j : Fin (m + 1)) : err i j =
      (rowR i j : ℂ) + Complex.I * (rowI i j : ℂ) +
      α⁻¹ * ((if i = 0 then u x j else 0) + (if j = 0 then u x i else 0)) := by
    have hp := actual_increment_physical_metric_row F hF chart heChart Ω hΩ hΩt hinj u νR νI τ
      x hx hu hνR hνI i j
    dsimp only at hp
    conv_lhs at hp =>
      simp only [νR, νI, Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul]
    dsimp only [err, WR, WI, ZR, ZI]
    simp_rw [incrementsModeFullReconstruction_tangent_normal]
    rw [hp]
    dsimp only [rowR, rowI, uR, uI, c]
    have ha : α⁻¹ = Complex.I / (τ : ℂ) := by dsimp [α]; rw [inv_div]
    rw [ha]
    push_cast
    ring
  constructor
  · have hr := increments_mode_complex_first_row F hF c u α hR hI vfR vfI x
    change (rowR 0 0 : ℂ) + Complex.I * (rowI 0 0 : ℂ) +
      2 * α⁻¹ * u x 0 = 2 * e 0 at hr
    rw [hphys]
    simp only [ite_true]
    calc
      _ = (rowR 0 0 : ℂ) + Complex.I * (rowI 0 0 : ℂ) + 2 * α⁻¹ * u x 0 := by ring
      _ = _ := hr
  constructor
  · intro a
    have hr := increments_mode_complex_mixed_row F hF c u α hR hI vfR vfI x a
    change (rowR 0 a.succ : ℂ) + Complex.I * (rowI 0 a.succ : ℂ) +
      α⁻¹ * u x a.succ = e a.succ at hr
    rw [hphys]
    simpa only [Fin.succ_ne_zero, ite_false, ite_true, add_zero] using hr
  · intro q
    have hr := increments_mode_complex_transverse_row F hF c u hR hI vfR vfI x
      hG hfreeR hfreeI q
    change (rowR q.val.1.succ q.val.2.succ : ℂ) +
      Complex.I * (rowI q.val.1.succ q.val.2.succ : ℂ) = 0 at hr
    rw [hphys]
    simpa only [Fin.succ_ne_zero, ite_false, add_zero, mul_zero] using hr

end ActualChart
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_increment_chart_derivative_injective
#print axioms GlobalEmbedding.Continuation.actual_increment_physical_metric_row
#print axioms GlobalEmbedding.Continuation.actual_increment_physical_residual_rows
