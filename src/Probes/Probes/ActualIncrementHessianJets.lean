import Probes.ActualIncrementChartGeometry
import Smoothing.WeightedActualProjection
import Smoothing.WeightedActualOperations

/-!
# Actual projected Hessian jets from the same first and second spatial jets

The input bounds concern actual derivatives of `F p ∘ (e p).symm` on the
same joint open domain. The normal projection and projected Hessian bounds
are outputs. The fixed operator norm in the constant retains all native
norm conventions and depends only on the model spaces, never on chart count.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

def actualIncrementPostcomposeHessian (E V : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] :
    (V →L[ℝ] V) →L[ℝ] (E →L[ℝ] E →L[ℝ] V) →L[ℝ] (E →L[ℝ] E →L[ℝ] V) :=
  (ContinuousLinearMap.compL ℝ E (E →L[ℝ] V) (E →L[ℝ] V)).comp
    (ContinuousLinearMap.compL ℝ E V V)

def actualIncrementProjectionConstant (j : ℕ) (c MA : ℝ) : ℝ :=
  1 + 2^j * (2^j * MA * slowInverseMajorant c⁻¹ (2^j * MA^2) j) * MA

def actualIncrementSecondFormConstant (_m _N j : ℕ) (c MA MH : ℝ) : ℝ :=
  2^j * actualIncrementProjectionConstant j c MA * MH

section PairingNorm
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
local instance postcomposeEVNormed : NormedAddCommGroup (E →L[ℝ] V) := inferInstance
local instance postcomposeEVSpace : NormedSpace ℝ (E →L[ℝ] V) := inferInstance
local instance postcomposeVVNormed : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
local instance postcomposeVVSpace : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
local instance postcomposeIntermediateNormed : NormedAddCommGroup ((E →L[ℝ] V) →L[ℝ] E →L[ℝ] V) := inferInstance
local instance postcomposeIntermediateSpace : NormedSpace ℝ ((E →L[ℝ] V) →L[ℝ] E →L[ℝ] V) := inferInstance
local instance postcomposeHessianNormed : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] V) := inferInstance
local instance postcomposeHessianSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] V) := inferInstance

theorem actualIncrementPostcomposeHessian_norm_le :
    ‖actualIncrementPostcomposeHessian E V‖ ≤ 1 := by
  let L₀ := ContinuousLinearMap.compL ℝ E (E →L[ℝ] V) (E →L[ℝ] V)
  let L₁ := ContinuousLinearMap.compL ℝ E V V
  change ‖L₀.comp L₁‖ ≤ 1
  have h₀ : ‖L₀‖ ≤ 1 := ContinuousLinearMap.norm_compL_le ℝ E (E →L[ℝ] V) (E →L[ℝ] V)
  have h₁ : ‖L₁‖ ≤ 1 := ContinuousLinearMap.norm_compL_le ℝ E V V
  exact (ContinuousLinearMap.opNorm_comp_le L₀ L₁).trans
    (by simpa using mul_le_mul h₀ h₁ L₁.opNorm_nonneg zero_le_one)
end PairingNorm

theorem actualIncrementProjectionConstant_nonneg (j : ℕ) {c MA : ℝ}
    (hc : 0 < c) (hMA : 0 ≤ MA) :
    0 ≤ actualIncrementProjectionConstant j c MA := by
  have hR := slowInverseMajorant_nonneg (inv_nonneg.mpr hc.le)
    (by positivity : 0 ≤ 2^j * MA^2) j
  unfold actualIncrementProjectionConstant
  positivity

theorem actualIncrementSecondFormConstant_nonneg (m N j : ℕ) {c MA MH : ℝ}
    (hc : 0 < c) (hMA : 0 ≤ MA) (hMH : 0 ≤ MH) :
    0 ≤ actualIncrementSecondFormConstant m N j c MA MH := by
  have hp := actualIncrementProjectionConstant_nonneg j hc hMA
  unfold actualIncrementSecondFormConstant
  positivity

variable {m N : ℕ} {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ, D)
local instance incrementDVNormed : NormedAddCommGroup (D →L[ℝ] V) := inferInstance
local instance incrementDVSpace : NormedSpace ℝ (D →L[ℝ] V) := inferInstance
local instance incrementVVNormed : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
local instance incrementVVSpace : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
local instance incrementHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := inferInstance
local instance incrementHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) := inferInstance
local instance incrementIntermediateNormed : NormedAddCommGroup ((D →L[ℝ] V) →L[ℝ] D →L[ℝ] V) := inferInstance
local instance incrementIntermediateSpace : NormedSpace ℝ ((D →L[ℝ] V) →L[ℝ] D →L[ℝ] V) := inferInstance
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) M]

/-- The original normal projection acquires its joint slow-jet budget from
the actual first derivative and a fixed singular reserve. -/
theorem actual_increment_normal_projection_slow_jets
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    (e : Ep → OpenPartialHomeomorph M D)
    (he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set X) (hO : IsOpen O) (hcoord : ∀ z ∈ O, z.2 ∈ (e z.1).target)
    (hA : ContDiffOn ℝ ∞ (fun z : X => fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2) O)
    (j : ℕ) (ell c MA : ℝ) (hell : 0 < ell) (hc : 0 < c) (hMA : 0 ≤ MA)
    (hreserve : ∀ z ∈ O, ∀ v : D,
      c * ‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2 v‖^2)
    (hAj : ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (F y.1 ∘ (e y.1).symm) y.2) z‖ ≤ MA) :
    ContDiffOn ℝ ∞ (fun z : X =>
      (normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2)).starProjection) O ∧
    ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k
      (fun y : X => (normalSpace (I := 𝓙) (F y.1) ((e y.1).symm y.2)).starProjection) z‖ ≤
        actualIncrementProjectionConstant j c MA := by
  let A : X → D →L[ℝ] V := fun z => fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2
  let P : X → V →L[ℝ] V := fun z => (LinearMap.range (A z).toLinearMap)ᗮ.starProjection
  obtain ⟨hP,hPb⟩ := actual_normal_projection_slow_jets A O hO hA j ell c MA
    hell hc hMA hreserve hAj
  have heq : ∀ z ∈ O,
      (normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2)).starProjection = P z := by
    intro z hz
    rw [actual_increment_normalSpace_eq_chart_range (F z.1) (hF z.1) (e z.1)
      (he z.1) z.2 (hcoord z hz)]
  refine ⟨hP.congr heq, ?_⟩
  intro k hk z hz
  have hEq : (fun y : X =>
      (normalSpace (I := 𝓙) (F y.1) ((e y.1).symm y.2)).starProjection) =ᶠ[𝓝 z] P :=
    Filter.eventuallyEq_of_mem (hO.mem_nhds hz) (fun y hy => heq y hy)
  rw [(hEq.iteratedFDeriv ℝ k).eq_of_nhds]
  exact hPb k hk z hz

/-- The actual projected coordinate Hessian has all fixed-order joint slow
jets from the true first/Hessian profiles and the same first-frame reserve. -/
theorem actual_increment_projected_hessian_slow_jets
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    (e : Ep → OpenPartialHomeomorph M D)
    (he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set X) (hO : IsOpen O) (hcoord : ∀ z ∈ O, z.2 ∈ (e z.1).target)
    (hA : ContDiffOn ℝ ∞ (fun z : X => fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2) O)
    (hH : ContDiffOn ℝ ∞ (fun z : X =>
      fderiv ℝ (fderiv ℝ (F z.1 ∘ (e z.1).symm)) z.2) O)
    (j : ℕ) (ell c MA MH : ℝ) (hell : 0 < ell) (hc : 0 < c)
    (hMA : 0 ≤ MA) (hMH : 0 ≤ MH)
    (hreserve : ∀ z ∈ O, ∀ v : D,
      c * ‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2 v‖^2)
    (hAj : ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (F y.1 ∘ (e y.1).symm) y.2) z‖ ≤ MA)
    (hHj : ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (fderiv ℝ (F y.1 ∘ (e y.1).symm)) y.2) z‖ ≤ MH) :
    let Q : X → D →L[ℝ] D →L[ℝ] V := fun z =>
      actualIncrementPostcomposeHessian D V
        (normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2)).starProjection
        (fderiv ℝ (fderiv ℝ (F z.1 ∘ (e z.1).symm)) z.2)
    ContDiffOn ℝ ∞ Q O ∧
    ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k Q z‖ ≤
      actualIncrementSecondFormConstant m N j c MA MH := by
  dsimp only
  let P : X → V →L[ℝ] V := fun z =>
    (normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2)).starProjection
  let H : X → D →L[ℝ] D →L[ℝ] V := fun z =>
    fderiv ℝ (fderiv ℝ (F z.1 ∘ (e z.1).symm)) z.2
  let L := actualIncrementPostcomposeHessian D V
  obtain ⟨hP,hPb⟩ := actual_increment_normal_projection_slow_jets F hF e he O hO hcoord
    hA j ell c MA hell hc hMA hreserve hAj
  have hQ : ContDiffOn ℝ ∞ (fun z => L (P z) (H z)) O := by
    change ContDiffOn ℝ ∞ (fun z =>
      (ContinuousLinearMap.compL ℝ D V V (P z)).comp (H z)) O
    have hp : ContDiffOn ℝ ∞ (fun z => ContinuousLinearMap.compL ℝ D V V (P z)) O :=
      (ContinuousLinearMap.compL ℝ D V V).contDiff.comp_contDiffOn hP
    exact hp.clm_comp hH
  refine ⟨hQ, ?_⟩
  intro k hk z hz
  have hb := slow_bilinear_jet_bound L
    (@actualIncrementPostcomposeHessian_norm_le D V _ _ _ _) O hO P H hP hH k ell
    (actualIncrementProjectionConstant j c MA) MH hell.le
    (actualIncrementProjectionConstant_nonneg j hc hMA) z hz
    (fun r hr => hPb r (hr.trans hk) z hz) (fun r hr => hHj r (hr.trans hk) z hz)
  apply hb.trans
  unfold actualIncrementSecondFormConstant
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk)
      (actualIncrementProjectionConstant_nonneg j hc hMA)) hMH

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_increment_normal_projection_slow_jets
#print axioms GlobalEmbedding.Continuation.actual_increment_projected_hessian_slow_jets
