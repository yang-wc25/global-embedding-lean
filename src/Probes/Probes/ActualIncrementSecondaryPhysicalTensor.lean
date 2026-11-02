import Probes.ActualIncrementSecondaryPhysicalRows

/-! The complete actual symmetric tensor residual follows from the original
11, mixed and once-sorted transverse physical rows. This retains the literal
induced-metric derivative, actual finite polynomial and true source channels. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Function
open scoped ContDiff
namespace GlobalEmbedding.Continuation

/-- Symmetry of the actual derivative of the original induced metric needs no
extra regularity hypothesis. -/
theorem actual_increment_coordinate_metric_variation_symm {n N : ℕ}
    (F Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (x v w : EuclideanSpace ℝ (Fin n)) :
    incrementsCoordinateMetricVariation F Z x v w =
      incrementsCoordinateMetricVariation F Z x w v := by
  unfold incrementsCoordinateMetricVariation
  congr 1
  funext s
  simp only [inducedMetric_apply, innerₗ_apply_apply]
  exact real_inner_comm _ _

/-- The original once-sorted transverse rows determine every tensor entry. -/
theorem actual_increment_symmetric_rows_complete {m : ℕ}
    (err : Fin (m+1) → Fin (m+1) → ℂ) (v : Fin (m+1) → ℂ)
    (hsymm : ∀ i j, err i j = err j i)
    (h0 : err 0 0 = -2 * v 0)
    (h1 : ∀ a : Fin m, err 0 a.succ = -v a.succ)
    (ht : ∀ q : {t : Fin m × Fin m // t.1 ≤ t.2}, err q.val.1.succ q.val.2.succ = 0) :
    ∀ i j, err i j = if i = 0 then (if j = 0 then -2 * v 0 else -v j)
      else if j = 0 then -v i else 0 := by
  intro i j
  refine Fin.cases ?_ (fun a => ?_) i
  · refine Fin.cases ?_ (fun b => ?_) j
    · simpa using h0
    · simpa using h1 b
  · refine Fin.cases ?_ (fun b => ?_) j
    · simpa [hsymm a.succ 0] using h1 a
    · simp only [Fin.succ_ne_zero, ↓reduceIte]
      rcases le_total a b with hab | hba
      · exact ht ⟨(a,b),hab⟩
      · rw [hsymm]
        exact ht ⟨(b,a),hba⟩

variable {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ, D)
local notation "Source" => Fin (m+1) → Fin (m+1) → ℝ
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) M]

theorem actual_secondary_mode_physical_tensor
    (F : M → V) (hF : ContMDiff 𝓙 𝓘(ℝ, V) ∞ F) (chart : OpenPartialHomeomorph M D)
    (hchart : chart ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set D) (hO : IsOpen O) (hOt : O ⊆ chart.target)
    (hinj : ∀ z ∈ O, Function.Injective
      (mfderiv 𝓙 𝓘(ℝ, V) F (chart.symm z)))
    (hfree : ∀ z ∈ O,
      let β := incrementsTransversePairing F hF (chart.symm z)
        (fun a : Fin m ↦ incrementsModeCoordinateDirections chart.symm z a.succ)
      (β.comp β.adjoint).IsInvertible)
    (hR hI : D → Source) (hhR : ContDiffOn ℝ ∞ hR O) (hhI : ContDiffOn ℝ ∞ hI O)
    (τ : ℝ) (hτ : 0 < τ) (p : ℕ) (x : D) (hx : x ∈ O)
    (hRsymm : ∀ i j, hR x i j = hR x j i)
    (hIsymm : ∀ i j, hI x i j = hI x j i) :
    let c := chart.symm
    let α := (τ : ℂ) / Complex.I
    let A := incrementsModeComplexFirstOrderA F hF c
    let B := incrementsModeComplexFirstOrderB F hF c
    let k := fun z ↦ incrementsModeComplexInclude
      (incrementsModeSource F hF c hR (fun _ ↦ 0) z) + Complex.I •
      incrementsModeComplexInclude (incrementsModeSource F hF c hI (fun _ ↦ 0) z)
    let U := incrementsActualModeSum A B α p k
    let ZR := incrementsModeFullReconstruction F hF c
      (fun z ↦ incrementsModeRealPart (U z)) hR (fun _ ↦ 0)
    let ZI := incrementsModeFullReconstruction F hF c
      (fun z ↦ incrementsModeImagPart (U z)) hI (fun _ ↦ 0)
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
    let v := ((incrementsActualModeStep A B α)^[p] k) x
    ∀ i j, err i j = if i = 0 then (if j = 0 then -2 * v 0 else -v j)
      else if j = 0 then -v i else 0 := by
  intro c α A B k U ZR ZI WR WI err v
  have hs : ∀ i j, err i j = err j i := by
    intro i j
    dsimp only [err]
    rw [actual_increment_coordinate_metric_variation_symm (F ∘ c) WR x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1),
      actual_increment_coordinate_metric_variation_symm (F ∘ c) WI x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1), hRsymm i j, hIsymm i j]
  obtain ⟨h0,h1,ht⟩ := actual_secondary_mode_physical_rows F hF chart hchart O hO hOt hinj hfree hR hI hhR hhI τ hτ p x hx
  refine actual_increment_symmetric_rows_complete err v hs ?_ ?_ ?_
  · simpa only [c, α, A, B, k, U, ZR, ZI, WR, WI, err, v] using h0
  · simpa only [c, α, A, B, k, U, ZR, ZI, WR, WI, err, v] using h1
  · simpa only [c, α, A, B, k, U, ZR, ZI, WR, WI, err, v] using ht

theorem actual_secondary_mode_physical_tensor_of_reserves
    (F : M → V) (hF : ContMDiff 𝓙 𝓘(ℝ, V) ∞ F) (chart : OpenPartialHomeomorph M D)
    (hchart : chart ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set D) (hO : IsOpen O) (hOt : O ⊆ chart.target)
    (cF cT : ℝ) (hcF : 0 < cF) (hcT : 0 < cT)
    (hfirst : ∀ z ∈ O, ∀ v : D,
      cF * ‖v‖^2 ≤ ‖fderiv ℝ (F ∘ chart.symm) z v‖^2)
    (htransverse : ∀ z ∈ O, ∀ v : EuclideanSpace ℝ {p : Fin m × Fin m // p.1 ≤ p.2},
      cT * ‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame F hF chart.symm z v‖^2)
    (hR hI : D → Source) (hhR : ContDiffOn ℝ ∞ hR O) (hhI : ContDiffOn ℝ ∞ hI O)
    (τ : ℝ) (hτ : 0 < τ) (p : ℕ) (x : D) (hx : x ∈ O)
    (hRsymm : ∀ i j, hR x i j = hR x j i)
    (hIsymm : ∀ i j, hI x i j = hI x j i) :
    let c := chart.symm
    let α := (τ : ℂ) / Complex.I
    let A := incrementsModeComplexFirstOrderA F hF c
    let B := incrementsModeComplexFirstOrderB F hF c
    let k := fun z ↦ incrementsModeComplexInclude
      (incrementsModeSource F hF c hR (fun _ ↦ 0) z) + Complex.I •
      incrementsModeComplexInclude (incrementsModeSource F hF c hI (fun _ ↦ 0) z)
    let U := incrementsActualModeSum A B α p k
    let ZR := incrementsModeFullReconstruction F hF c
      (fun z ↦ incrementsModeRealPart (U z)) hR (fun _ ↦ 0)
    let ZI := incrementsModeFullReconstruction F hF c
      (fun z ↦ incrementsModeImagPart (U z)) hI (fun _ ↦ 0)
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
    let v := ((incrementsActualModeStep A B α)^[p] k) x
    ∀ i j, err i j = if i = 0 then (if j = 0 then -2 * v 0 else -v j)
      else if j = 0 then -v i else 0 := by
  intro c α A B k U ZR ZI WR WI err v
  have hs : ∀ i j, err i j = err j i := by
    intro i j
    dsimp only [err]
    rw [actual_increment_coordinate_metric_variation_symm (F ∘ c) WR x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1),
      actual_increment_coordinate_metric_variation_symm (F ∘ c) WI x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1), hRsymm i j, hIsymm i j]
  obtain ⟨h0,h1,ht⟩ := actual_secondary_mode_physical_rows_of_reserves F hF chart hchart O hO hOt cF cT hcF hcT hfirst htransverse hR hI hhR hhI τ hτ p x hx
  refine actual_increment_symmetric_rows_complete err v hs ?_ ?_ ?_
  · simpa only [c, α, A, B, k, U, ZR, ZI, WR, WI, err, v] using h0
  · simpa only [c, α, A, B, k, U, ZR, ZI, WR, WI, err, v] using h1
  · simpa only [c, α, A, B, k, U, ZR, ZI, WR, WI, err, v] using ht

theorem actual_secondary_mode_physical_tensor_of_good_phase
    (F : M → V) (hF : ContMDiff 𝓙 𝓘(ℝ, V) ∞ F) (chart : OpenPartialHomeomorph M D)
    (hchart : chart ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set D) (hO : IsOpen O) (hOt : O ⊆ chart.target)
    (hinj : ∀ z ∈ O, Function.Injective
      (mfderiv 𝓙 𝓘(ℝ, V) F (chart.symm z)))
    (psi : M → ℝ)
    (hpsi : ∀ z ∈ O, MDifferentiableAt 𝓙 𝓘(ℝ, ℝ) psi (chart.symm z))
    (hadapt : ∀ z ∈ O, psi (chart.symm z) = z 0)
    (hgood : ∀ z ∈ O, GoodCovector F hF (chart.symm z)
      ((tangentSpaceCastModel 𝓘(ℝ, ℝ) (psi (chart.symm z))).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓘(ℝ, ℝ) psi (chart.symm z))))
    (hR hI : D → Source) (hhR : ContDiffOn ℝ ∞ hR O) (hhI : ContDiffOn ℝ ∞ hI O)
    (τ : ℝ) (hτ : 0 < τ) (p : ℕ) (x : D) (hx : x ∈ O)
    (hRsymm : ∀ i j, hR x i j = hR x j i)
    (hIsymm : ∀ i j, hI x i j = hI x j i) :
    let c := chart.symm
    let α := (τ : ℂ) / Complex.I
    let A := incrementsModeComplexFirstOrderA F hF c
    let B := incrementsModeComplexFirstOrderB F hF c
    let k := fun z ↦ incrementsModeComplexInclude
      (incrementsModeSource F hF c hR (fun _ ↦ 0) z) + Complex.I •
      incrementsModeComplexInclude (incrementsModeSource F hF c hI (fun _ ↦ 0) z)
    let U := incrementsActualModeSum A B α p k
    let ZR := incrementsModeFullReconstruction F hF c
      (fun z ↦ incrementsModeRealPart (U z)) hR (fun _ ↦ 0)
    let ZI := incrementsModeFullReconstruction F hF c
      (fun z ↦ incrementsModeImagPart (U z)) hI (fun _ ↦ 0)
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
    let v := ((incrementsActualModeStep A B α)^[p] k) x
    ∀ i j, err i j = if i = 0 then (if j = 0 then -2 * v 0 else -v j)
      else if j = 0 then -v i else 0 := by
  intro c α A B k U ZR ZI WR WI err v
  have hs : ∀ i j, err i j = err j i := by
    intro i j
    dsimp only [err]
    rw [actual_increment_coordinate_metric_variation_symm (F ∘ c) WR x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1),
      actual_increment_coordinate_metric_variation_symm (F ∘ c) WI x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1), hRsymm i j, hIsymm i j]
  obtain ⟨h0,h1,ht⟩ := actual_secondary_mode_physical_rows_of_good_phase F hF chart hchart O hO hOt hinj psi hpsi hadapt hgood hR hI hhR hhI τ hτ p x hx
  refine actual_increment_symmetric_rows_complete err v hs ?_ ?_ ?_
  · simpa only [c, α, A, B, k, U, ZR, ZI, WR, WI, err, v] using h0
  · simpa only [c, α, A, B, k, U, ZR, ZI, WR, WI, err, v] using h1
  · simpa only [c, α, A, B, k, U, ZR, ZI, WR, WI, err, v] using ht

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_secondary_mode_physical_tensor
#print axioms GlobalEmbedding.Continuation.actual_secondary_mode_physical_tensor_of_reserves
#print axioms GlobalEmbedding.Continuation.actual_secondary_mode_physical_tensor_of_good_phase
