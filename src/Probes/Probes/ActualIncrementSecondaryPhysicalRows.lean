import Probes.ActualIncrementChosenChartRegularity
import GlobalEmbedding.Paper.IncrementsSecondaryMode
import Probes.ActualIncrementGoodPhaseGeometry
import Probes.ActualIncrementReserveAdmissibility

/-!
# Actual secondary physical metric rows in the chosen adapted chart

The two forcing channels, actual finite polynomial, full inhomogeneous normal
reconstruction and modulated displacement are the original ones. All source,
solver and reconstructed-normal differentiability is produced from genuine
smooth/free geometry in the same maximal chart. The physical residual is the
actual finite iterate, with the original 11, mixed and transverse row factors.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Function
open scoped ContDiff
namespace GlobalEmbedding.Continuation

variable {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ, D)
local notation "Source" => Fin (m+1) → Fin (m+1) → ℝ
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) M]

/-- The original secondary displacement in the actual chosen chart has
physical errors -2v, -v and zero, where v is its genuine p-th finite iterate.
No source, coefficient or reconstructed-normal output regularity is assumed. -/
theorem actual_secondary_mode_physical_rows
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
    (τ : ℝ) (hτ : 0 < τ) (p : ℕ) (x : D) (hx : x ∈ O) :
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
    err 0 0 = -2 * v 0 ∧ (∀ a : Fin m, err 0 a.succ = -v a.succ) ∧
      ∀ q : {t : Fin m × Fin m // t.1 ≤ t.2}, err q.val.1.succ q.val.2.succ = 0 := by
  intro c α A B k U ZR ZI WR WI err v
  let uR := fun z ↦ incrementsModeRealPart (U z)
  let uI := fun z ↦ incrementsModeImagPart (U z)
  let e := α⁻¹ • U x + incrementsModeComplexReducedOperator F hF c U x - k x
  let νR := fun z ↦ (0 : normalSpace (I := 𝓙) F (c z)) +
    incrementsModeCoordinateJ F hF c z (incrementsModeTransverseTensor F c uR z) -
      (1 / 2 : ℝ) • incrementsModeCoordinateJ F hF c z (incrementsModeTransverseSource hR z)
  let νI := fun z ↦ (0 : normalSpace (I := 𝓙) F (c z)) +
    incrementsModeCoordinateJ F hF c z (incrementsModeTransverseTensor F c uI z) -
      (1 / 2 : ℝ) • incrementsModeCoordinateJ F hF c z (incrementsModeTransverseSource hI z)
  obtain ⟨hBR,hJ,hT,hA,hB⟩ := actual_increment_chosen_chart_coefficients_contDiffOn
    F hF chart hchart O hO hOt hinj hfree
  have hk := incrementsModeComplexSource_zeroFree_contDiffOn F hF c hR hI O hBR hJ hhR hhI
  have hu : ContDiffOn ℝ ∞ U O :=
    increments_actual_mode_sum_contDiffOn A B α p k O hO hA hB hk
  have hur : ContDiffOn ℝ ∞ uR O := incrementsModeRealPart.contDiff.comp_contDiffOn hu
  have hui : ContDiffOn ℝ ∞ uI O := incrementsModeImagPart.contDiff.comp_contDiffOn hu
  have hνR : ContDiffOn ℝ ∞ (fun z ↦ (νR z : V)) O := by
    have ht := incrementsModeTransverseTensor_contDiffOn F c O hO hT uR hur
    have hh := incrementsModeTransverseSourceCLM.contDiff.comp_contDiffOn hhR
    simpa only [νR, Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul,
      Submodule.coe_zero, zero_add, Function.comp_apply, ContinuousLinearMap.comp_apply,
      Submodule.subtypeL_apply, ← incrementsModeTransverseSource_eq_selector] using
      (hJ.clm_apply ht).sub ((hJ.clm_apply hh).const_smul (1 / 2 : ℝ))
  have hνI : ContDiffOn ℝ ∞ (fun z ↦ (νI z : V)) O := by
    have ht := incrementsModeTransverseTensor_contDiffOn F c O hO hT uI hui
    have hh := incrementsModeTransverseSourceCLM.contDiff.comp_contDiffOn hhI
    simpa only [νI, Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul,
      Submodule.coe_zero, zero_add, Function.comp_apply, ContinuousLinearMap.comp_apply,
      Submodule.subtypeL_apply, ← incrementsModeTransverseSource_eq_selector] using
      (hJ.clm_apply ht).sub ((hJ.clm_apply hh).const_smul (1 / 2 : ℝ))
  have hd := (hu.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hr := actual_increment_physical_residual_rows F hF chart hchart O hO hOt hinj U hR hI
    (fun _ ↦ 0) (fun _ ↦ 0) τ x hx hd (hfree x hx) (map_zero _) (map_zero _)
  dsimp only at hr
  have hdνR := (hνR.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hdνI := (hνI.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  specialize hr hdνR hdνI
  change err 0 0 = 2 * e 0 ∧ (∀ a : Fin m, err 0 a.succ = e a.succ) ∧
    ∀ q : {t : Fin m × Fin m // t.1 ≤ t.2}, err q.val.1.succ q.val.2.succ = 0 at hr
  have hα : α ≠ 0 := by
    dsimp [α]
    exact div_ne_zero (by exact_mod_cast hτ.ne') Complex.I_ne_zero
  have he := incrementsModeActualFiniteResidual_eq F hF c α hα p k O hO hA hB hk x hx
  change e = -v at he
  rcases hr with ⟨hr0, hr1, hrt⟩
  refine ⟨?_, ?_, hrt⟩
  · rw [he] at hr0
    simpa only [Pi.neg_apply, mul_neg, neg_mul] using hr0
  · intro a
    have ha := hr1 a
    rw [he] at ha
    simpa only [Pi.neg_apply] using ha

/-- Genuine primitive frame reserves supply all original geometric admissibility
needed for the exact actual secondary physical residual. -/
theorem actual_secondary_mode_physical_rows_of_reserves
    (F : M → V) (hF : ContMDiff 𝓙 𝓘(ℝ, V) ∞ F) (chart : OpenPartialHomeomorph M D)
    (hchart : chart ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set D) (hO : IsOpen O) (hOt : O ⊆ chart.target)
    (cF cT : ℝ) (hcF : 0 < cF) (hcT : 0 < cT)
    (hfirst : ∀ z ∈ O, ∀ v : D,
      cF * ‖v‖^2 ≤ ‖fderiv ℝ (F ∘ chart.symm) z v‖^2)
    (htransverse : ∀ z ∈ O, ∀ v : EuclideanSpace ℝ {p : Fin m × Fin m // p.1 ≤ p.2},
      cT * ‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame F hF chart.symm z v‖^2)
    (hR hI : D → Source) (hhR : ContDiffOn ℝ ∞ hR O) (hhI : ContDiffOn ℝ ∞ hI O)
    (τ : ℝ) (hτ : 0 < τ) (p : ℕ) (x : D) (hx : x ∈ O) :
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
    err 0 0 = -2 * v 0 ∧ (∀ a : Fin m, err 0 a.succ = -v a.succ) ∧
      ∀ q : {t : Fin m × Fin m // t.1 ≤ t.2}, err q.val.1.succ q.val.2.succ = 0 := by
  exact actual_secondary_mode_physical_rows F hF chart hchart O hO hOt
    (fun z hz => actual_increment_manifold_injective_of_first_reserve F hF chart hchart z
      (hOt hz) cF hcF (hfirst z hz))
    (fun z hz => actual_increment_transverse_gram_of_reserve F hF chart.symm z cT hcT
      (htransverse z hz)) hR hI hhR hhI τ hτ p x hx

/-- Original Good of the literal adapted phase supplies the original transverse
Gram, so the exact actual secondary result needs no Gram hypothesis. -/
theorem actual_secondary_mode_physical_rows_of_good_phase
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
    (τ : ℝ) (hτ : 0 < τ) (p : ℕ) (x : D) (hx : x ∈ O) :
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
    err 0 0 = -2 * v 0 ∧ (∀ a : Fin m, err 0 a.succ = -v a.succ) ∧
      ∀ q : {t : Fin m × Fin m // t.1 ≤ t.2}, err q.val.1.succ q.val.2.succ = 0 := by
  exact actual_secondary_mode_physical_rows F hF chart hchart O hO hOt hinj
    (fun z hz => actual_increment_transverse_gram_of_good_phase F hF psi chart hchart O hO hOt
      z hz (hpsi z hz) hadapt (hgood z hz)) hR hI hhR hhI τ hτ p x hx

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_secondary_mode_physical_rows

#print axioms GlobalEmbedding.Continuation.actual_secondary_mode_physical_rows_of_reserves
#print axioms GlobalEmbedding.Continuation.actual_secondary_mode_physical_rows_of_good_phase
