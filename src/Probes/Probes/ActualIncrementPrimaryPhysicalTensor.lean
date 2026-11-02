import Probes.ActualIncrementChosenChartRegularity
import GlobalEmbedding.Paper.IncrementsSecondaryMode
import Probes.ActualIncrementGoodPhaseGeometry
import Probes.ActualIncrementReserveAdmissibility
import Probes.ActualIncrementSecondaryPhysicalTensor
import GlobalEmbedding.Paper.IncrementsModeJointSourceRegularity

/-! The actual primary h=0 physical tensor with arbitrary genuine free-normal
channels. Both channels retain their literal original amplitudes and signs;
normal smoothness is derived from primitive smooth free fields and geometry.
The same chosen adapted chart, finite polynomial and full reconstruction occur
throughout. No output physical identity or normal regularity is an input. -/

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

theorem actual_primary_mode_physical_tensor
    (F : M → V) (hF : ContMDiff 𝓙 𝓘(ℝ, V) ∞ F) (chart : OpenPartialHomeomorph M D)
    (hchart : chart ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set D) (hO : IsOpen O) (hOt : O ⊆ chart.target)
    (hinj : ∀ z ∈ O, Function.Injective
      (mfderiv 𝓙 𝓘(ℝ, V) F (chart.symm z)))
    (hfree : ∀ z ∈ O,
      let β := incrementsTransversePairing F hF (chart.symm z)
        (fun a : Fin m ↦ incrementsModeCoordinateDirections chart.symm z a.succ)
      (β.comp β.adjoint).IsInvertible)
    (vfR vfI : (x : D) → normalSpace (I := 𝓙) F (chart.symm x))
    (hvfR : ContDiffOn ℝ ∞ (fun x => (vfR x : V)) O)
    (hvfI : ContDiffOn ℝ ∞ (fun x => (vfI x : V)) O)
    (hkernelR : ∀ x ∈ O, incrementsTransversePairing F hF (chart.symm x)
      (fun a : Fin m => incrementsModeCoordinateDirections chart.symm x a.succ) (vfR x) = 0)
    (hkernelI : ∀ x ∈ O, incrementsTransversePairing F hF (chart.symm x)
      (fun a : Fin m => incrementsModeCoordinateDirections chart.symm x a.succ) (vfI x) = 0)
    (τ : ℝ) (hτ : 0 < τ) (p : ℕ) (x : D) (hx : x ∈ O) :
    let c := chart.symm
    let α := (τ : ℂ) / Complex.I
    let A := incrementsModeComplexFirstOrderA F hF c
    let B := incrementsModeComplexFirstOrderB F hF c
    let k := fun z ↦ incrementsModeComplexInclude
      (incrementsModeSource F hF c (fun _ _ _ => 0) vfR z) + Complex.I •
      incrementsModeComplexInclude (incrementsModeSource F hF c (fun _ _ _ => 0) vfI z)
    let U := incrementsActualModeSum A B α p k
    let ZR := incrementsModeFullReconstruction F hF c
      (fun z ↦ incrementsModeRealPart (U z)) (fun _ _ _ => 0) vfR
    let ZI := incrementsModeFullReconstruction F hF c
      (fun z ↦ incrementsModeImagPart (U z)) (fun _ _ _ => 0) vfI
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
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) : ℂ))
    let v := ((incrementsActualModeStep A B α)^[p] k) x
    ∀ i j, err i j = if i = 0 then (if j = 0 then -2*v 0 else -v j)
      else if j = 0 then -v i else 0 := by
  intro c α A B k U ZR ZI WR WI err v
  let uR := fun z => incrementsModeRealPart (U z)
  let uI := fun z => incrementsModeImagPart (U z)
  let e := α⁻¹ • U x + incrementsModeComplexReducedOperator F hF c U x - k x
  let νR := fun z => vfR z + incrementsModeCoordinateJ F hF c z
    (incrementsModeTransverseTensor F c uR z) - (1/2 : ℝ) •
      incrementsModeCoordinateJ F hF c z (incrementsModeTransverseSource (fun _ _ _ => 0) z)
  let νI := fun z => vfI z + incrementsModeCoordinateJ F hF c z
    (incrementsModeTransverseTensor F c uI z) - (1/2 : ℝ) •
      incrementsModeCoordinateJ F hF c z (incrementsModeTransverseSource (fun _ _ _ => 0) z)
  obtain ⟨hBR,hJ,hT,hA,hB⟩ := actual_increment_chosen_chart_coefficients_contDiffOn
    F hF chart hchart O hO hOt hinj hfree
  have sourceSmooth (vf : (x : D) → normalSpace (I := 𝓙) F (c x))
      (hvf : ContDiffOn ℝ ∞ (fun x => (vf x : V)) O) :
      ContDiffOn ℝ ∞ (fun z => incrementsModeSource F hF c (fun _ _ _ => 0) vf z) O := by
    have hz := incrementsModeSource_zeroFree_contDiffOn F hF c (fun _ _ _ => 0)
      O hBR hJ contDiffOn_const
    have hq := incrementsModeForcingSourcePairing.contDiff.comp_contDiffOn hBR
    apply (hz.add ((hq.clm_apply hvf).const_smul (2 : ℝ))).congr
    intro z hz
    exact incrementsModeSource_eq_zeroFree_add F hF c (fun _ _ _ => 0) vf z
  have hk : ContDiffOn ℝ ∞ k O :=
    (incrementsModeComplexInclude.contDiff.comp_contDiffOn (sourceSmooth vfR hvfR)).add
      ((incrementsModeComplexInclude.contDiff.comp_contDiffOn (sourceSmooth vfI hvfI)).const_smul Complex.I)
  have hu : ContDiffOn ℝ ∞ U O :=
    increments_actual_mode_sum_contDiffOn A B α p k O hO hA hB hk
  have hur : ContDiffOn ℝ ∞ uR O := incrementsModeRealPart.contDiff.comp_contDiffOn hu
  have hui : ContDiffOn ℝ ∞ uI O := incrementsModeImagPart.contDiff.comp_contDiffOn hu
  have hzT (z : D) : incrementsModeTransverseSource (fun _ _ _ => (0 : ℝ)) z = 0 := by
    ext q
    simp [incrementsModeTransverseSource]
  have hνR : ContDiffOn ℝ ∞ (fun z => (νR z : V)) O := by
    have ht := incrementsModeTransverseTensor_contDiffOn F c O hO hT uR hur
    simpa only [νR,Submodule.coe_add,Submodule.coe_sub,Submodule.coe_smul,
      hzT, map_zero, Submodule.coe_zero, smul_zero, sub_zero,
      ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] using hvfR.add (hJ.clm_apply ht)
  have hνI : ContDiffOn ℝ ∞ (fun z => (νI z : V)) O := by
    have ht := incrementsModeTransverseTensor_contDiffOn F c O hO hT uI hui
    simpa only [νI,Submodule.coe_add,Submodule.coe_sub,Submodule.coe_smul,
      hzT, map_zero, Submodule.coe_zero, smul_zero, sub_zero,
      ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] using hvfI.add (hJ.clm_apply ht)
  have hd := (hu.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hr := actual_increment_physical_residual_rows F hF chart hchart O hO hOt hinj U
    (fun _ _ _ => 0) (fun _ _ _ => 0) vfR vfI τ x hx hd (hfree x hx)
    (hkernelR x hx) (hkernelI x hx)
  dsimp only at hr
  specialize hr ((hνR.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))
    ((hνI.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))
  have hrows : err 0 0 = 2*e 0 ∧ (∀ a : Fin m, err 0 a.succ = e a.succ) ∧
      ∀ q : {t : Fin m × Fin m // t.1 ≤ t.2}, err q.val.1.succ q.val.2.succ = 0 := by
    simpa only [Complex.ofReal_zero,mul_zero,add_zero,sub_zero] using hr
  have hα : α ≠ 0 := div_ne_zero (by exact_mod_cast hτ.ne') Complex.I_ne_zero
  have he := incrementsModeActualFiniteResidual_eq F hF c α hα p k O hO hA hB hk x hx
  change e = -v at he
  have hs : ∀ i j, err i j = err j i := by
    intro i j
    dsimp only [err]
    rw [actual_increment_coordinate_metric_variation_symm (F ∘ c) WR x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1),
      actual_increment_coordinate_metric_variation_symm (F ∘ c) WI x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)]
  apply actual_increment_symmetric_rows_complete err v hs
  · have h0 := hrows.1
    rw [he] at h0
    simpa only [Pi.neg_apply,mul_neg,neg_mul] using h0
  · intro a
    have h1 := hrows.2.1 a
    rw [he] at h1
    simpa only [Pi.neg_apply] using h1
  · exact hrows.2.2


theorem actual_primary_physical_tensor_eq_reduced
    (F : M → V) (hF : ContMDiff 𝓙 𝓘(ℝ, V) ∞ F) (chart : OpenPartialHomeomorph M D)
    (hchart : chart ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set D) (hO : IsOpen O) (hOt : O ⊆ chart.target)
    (hinj : ∀ z ∈ O, Function.Injective
      (mfderiv 𝓙 𝓘(ℝ, V) F (chart.symm z)))
    (hfree : ∀ z ∈ O,
      let β := incrementsTransversePairing F hF (chart.symm z)
        (fun a : Fin m ↦ incrementsModeCoordinateDirections chart.symm z a.succ)
      (β.comp β.adjoint).IsInvertible)
    (vfR vfI : (x : D) → normalSpace (I := 𝓙) F (chart.symm x))
    (hvfR : ContDiffOn ℝ ∞ (fun x => (vfR x : V)) O)
    (hvfI : ContDiffOn ℝ ∞ (fun x => (vfI x : V)) O)
    (hkernelR : ∀ x ∈ O, incrementsTransversePairing F hF (chart.symm x)
      (fun a : Fin m => incrementsModeCoordinateDirections chart.symm x a.succ) (vfR x) = 0)
    (hkernelI : ∀ x ∈ O, incrementsTransversePairing F hF (chart.symm x)
      (fun a : Fin m => incrementsModeCoordinateDirections chart.symm x a.succ) (vfI x) = 0)
    (u : D → Fin (m+1) → ℂ) (hu : ContDiffOn ℝ ∞ u O)
    (τ : ℝ) (x : D) (hx : x ∈ O) :
    let c := chart.symm
    let α := (τ : ℂ) / Complex.I
    let k := fun z ↦ incrementsModeComplexInclude
      (incrementsModeSource F hF c (fun _ _ _ => 0) vfR z) + Complex.I •
      incrementsModeComplexInclude (incrementsModeSource F hF c (fun _ _ _ => 0) vfI z)
    let ZR := incrementsModeFullReconstruction F hF c
      (fun z ↦ incrementsModeRealPart (u z)) (fun _ _ _ => 0) vfR
    let ZI := incrementsModeFullReconstruction F hF c
      (fun z ↦ incrementsModeImagPart (u z)) (fun _ _ _ => 0) vfI
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
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) : ℂ))
    let e := α⁻¹ • u x + incrementsModeComplexReducedOperator F hF c u x-k x
    ∀ i j, err i j = if i = 0 then (if j = 0 then 2*e 0 else e j)
      else if j = 0 then e i else 0 := by
  intro c α k ZR ZI WR WI err e
  let uR := fun z => incrementsModeRealPart (u z)
  let uI := fun z => incrementsModeImagPart (u z)
  let νR := fun z => vfR z + incrementsModeCoordinateJ F hF c z
    (incrementsModeTransverseTensor F c uR z) - (1/2 : ℝ) •
      incrementsModeCoordinateJ F hF c z (incrementsModeTransverseSource (fun _ _ _ => 0) z)
  let νI := fun z => vfI z + incrementsModeCoordinateJ F hF c z
    (incrementsModeTransverseTensor F c uI z) - (1/2 : ℝ) •
      incrementsModeCoordinateJ F hF c z (incrementsModeTransverseSource (fun _ _ _ => 0) z)
  obtain ⟨hBR,hJ,hT,hA,hB⟩ := actual_increment_chosen_chart_coefficients_contDiffOn
    F hF chart hchart O hO hOt hinj hfree
  have hur : ContDiffOn ℝ ∞ uR O := incrementsModeRealPart.contDiff.comp_contDiffOn hu
  have hui : ContDiffOn ℝ ∞ uI O := incrementsModeImagPart.contDiff.comp_contDiffOn hu
  have hzT (z : D) : incrementsModeTransverseSource (fun _ _ _ => (0 : ℝ)) z = 0 := by
    ext q
    simp [incrementsModeTransverseSource]
  have hνR : ContDiffOn ℝ ∞ (fun z => (νR z : V)) O := by
    have ht := incrementsModeTransverseTensor_contDiffOn F c O hO hT uR hur
    simpa only [νR,Submodule.coe_add,Submodule.coe_sub,Submodule.coe_smul,
      hzT, map_zero, Submodule.coe_zero, smul_zero, sub_zero,
      ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] using hvfR.add (hJ.clm_apply ht)
  have hνI : ContDiffOn ℝ ∞ (fun z => (νI z : V)) O := by
    have ht := incrementsModeTransverseTensor_contDiffOn F c O hO hT uI hui
    simpa only [νI,Submodule.coe_add,Submodule.coe_sub,Submodule.coe_smul,
      hzT, map_zero, Submodule.coe_zero, smul_zero, sub_zero,
      ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] using hvfI.add (hJ.clm_apply ht)
  have hd := (hu.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hr := actual_increment_physical_residual_rows F hF chart hchart O hO hOt hinj u
    (fun _ _ _ => 0) (fun _ _ _ => 0) vfR vfI τ x hx hd (hfree x hx)
    (hkernelR x hx) (hkernelI x hx)
  dsimp only at hr
  specialize hr ((hνR.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))
    ((hνI.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))
  have hrows : err 0 0 = 2*e 0 ∧ (∀ a : Fin m, err 0 a.succ = e a.succ) ∧
      ∀ q : {t : Fin m × Fin m // t.1 ≤ t.2}, err q.val.1.succ q.val.2.succ = 0 := by
    simpa only [Complex.ofReal_zero,mul_zero,add_zero,sub_zero] using hr
  have hs : ∀ i j, err i j = err j i := by
    intro i j
    dsimp only [err]
    rw [actual_increment_coordinate_metric_variation_symm (F ∘ c) WR x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1),
      actual_increment_coordinate_metric_variation_symm (F ∘ c) WI x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)]
  have hall := actual_increment_symmetric_rows_complete err (-e) hs
    (by simpa only [Pi.neg_apply,mul_neg,neg_mul,neg_neg] using hrows.1)
    (by intro a; simpa only [Pi.neg_apply,neg_neg] using hrows.2.1 a) hrows.2.2
  intro i j
  simpa only [Pi.neg_apply,mul_neg,neg_mul,neg_neg] using hall i j

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_primary_mode_physical_tensor

#print axioms GlobalEmbedding.Continuation.actual_primary_physical_tensor_eq_reduced
