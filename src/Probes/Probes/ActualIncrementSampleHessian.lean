import Probes.ActualIncrementHessianJets
import Probes.ActualIncrementSampleProjection

/-! The true projected Hessian is estimated only on the original samples,
with smoothness on its genuine open domain and exactly the same constants. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ, D)
local instance sampleIncrementDVNormed : NormedAddCommGroup (D →L[ℝ] V) := inferInstance
local instance sampleIncrementDVSpace : NormedSpace ℝ (D →L[ℝ] V) := inferInstance
local instance sampleIncrementVVNormed : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
local instance sampleIncrementVVSpace : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
local instance sampleIncrementHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := inferInstance
local instance sampleIncrementHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) := inferInstance
local instance sampleIncrementIntermediateNormed : NormedAddCommGroup ((D →L[ℝ] V) →L[ℝ] D →L[ℝ] V) := inferInstance
local instance sampleIncrementIntermediateSpace : NormedSpace ℝ ((D →L[ℝ] V) →L[ℝ] D →L[ℝ] V) := inferInstance
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) M]

theorem actual_increment_normal_projection_slow_jets_on_samples
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    (e : Ep → OpenPartialHomeomorph M D)
    (he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O) (hcoord : ∀ z ∈ O, z.2 ∈ (e z.1).target)
    (hA : ContDiffOn ℝ ∞ (fun z : X => fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2) O)
    (hinj : ∀ z ∈ O, Function.Injective (fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2))
    (j : ℕ) (ell c MA : ℝ) (hell : 0 < ell) (hc : 0 < c) (hMA : 0 ≤ MA)
    (hreserve : ∀ z ∈ S, ∀ v : D,
      c * ‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2 v‖^2)
    (hAj : ∀ k ≤ j, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (F y.1 ∘ (e y.1).symm) y.2) z‖ ≤ MA) :
    ContDiffOn ℝ ∞ (fun z : X =>
      (normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2)).starProjection) O ∧
    ∀ k ≤ j, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun y : X => (normalSpace (I := 𝓙) (F y.1) ((e y.1).symm y.2)).starProjection) z‖ ≤
        actualIncrementProjectionConstant j c MA := by
  let A : X → D →L[ℝ] V := fun z => fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2
  let P : X → V →L[ℝ] V := fun z => (LinearMap.range (A z).toLinearMap)ᗮ.starProjection
  obtain ⟨hP,hPb⟩ := actual_normal_projection_slow_jets_on_samples A O S hO hSO hA hinj j ell c MA
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
    Filter.eventuallyEq_of_mem (hO.mem_nhds (hSO hz)) (fun y hy => heq y hy)
  rw [(hEq.iteratedFDeriv ℝ k).eq_of_nhds]
  exact hPb k hk z hz

theorem actual_increment_projected_hessian_slow_jets_on_samples
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    (e : Ep → OpenPartialHomeomorph M D)
    (he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O) (hcoord : ∀ z ∈ O, z.2 ∈ (e z.1).target)
    (hA : ContDiffOn ℝ ∞ (fun z : X => fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2) O)
    (hH : ContDiffOn ℝ ∞ (fun z : X =>
      fderiv ℝ (fderiv ℝ (F z.1 ∘ (e z.1).symm)) z.2) O)
    (hinj : ∀ z ∈ O, Function.Injective (fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2))
    (j : ℕ) (ell c MA MH : ℝ) (hell : 0 < ell) (hc : 0 < c)
    (hMA : 0 ≤ MA) (hMH : 0 ≤ MH)
    (hreserve : ∀ z ∈ S, ∀ v : D,
      c * ‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2 v‖^2)
    (hAj : ∀ k ≤ j, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (F y.1 ∘ (e y.1).symm) y.2) z‖ ≤ MA)
    (hHj : ∀ k ≤ j, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (fderiv ℝ (F y.1 ∘ (e y.1).symm)) y.2) z‖ ≤ MH) :
    let Q : X → D →L[ℝ] D →L[ℝ] V := fun z =>
      actualIncrementPostcomposeHessian D V
        (normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2)).starProjection
        (fderiv ℝ (fderiv ℝ (F z.1 ∘ (e z.1).symm)) z.2)
    ContDiffOn ℝ ∞ Q O ∧
    ∀ k ≤ j, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k Q z‖ ≤
      actualIncrementSecondFormConstant m N j c MA MH := by
  dsimp only
  let P : X → V →L[ℝ] V := fun z =>
    (normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2)).starProjection
  let H : X → D →L[ℝ] D →L[ℝ] V := fun z =>
    fderiv ℝ (fderiv ℝ (F z.1 ∘ (e z.1).symm)) z.2
  let L := actualIncrementPostcomposeHessian D V
  obtain ⟨hP,hPb⟩ := actual_increment_normal_projection_slow_jets_on_samples F hF e he O S hO hSO hcoord
    hA hinj j ell c MA hell hc hMA hreserve hAj
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
    (actualIncrementProjectionConstant_nonneg j hc hMA) z (hSO hz)
    (fun r hr => hPb r (hr.trans hk) z hz) (fun r hr => hHj r (hr.trans hk) z hz)
  apply hb.trans
  unfold actualIncrementSecondFormConstant
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk)
      (actualIncrementProjectionConstant_nonneg j hc hMA)) hMH

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_increment_normal_projection_slow_jets_on_samples
#print axioms GlobalEmbedding.Continuation.actual_increment_projected_hessian_slow_jets_on_samples
