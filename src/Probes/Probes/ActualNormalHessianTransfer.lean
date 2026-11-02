import Probes.ActualNormalHessianTransition
import Probes.ActualIncrementTrueBJets

/-!
# True second-form budgets in adapted charts from the original geometry

The original coordinate first/Hessian bounds produce the original normal
Hessian. Its true two-frame pullback, rather than the ordinary transformed
Hessian, supplies the adapted chart's second form with shift zero.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Filter
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

private local instance rowFirstNormed (m N : ℕ) : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin N)) := inferInstance
private local instance rowFirstSpace (m N : ℕ) : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin N)) := inferInstance
private local instance rowHessianNormed (m N : ℕ) : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin N)) := inferInstance
private local instance rowHessianSpace (m N : ℕ) : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin N)) := inferInstance
private local instance rowPiNormed (m N : ℕ) : NormedAddCommGroup
    (Fin (m+1) → EuclideanSpace ℝ (Fin N)) := inferInstance
private local instance rowPiSpace (m N : ℕ) : NormedSpace ℝ
    (Fin (m+1) → EuclideanSpace ℝ (Fin N)) := inferInstance
private local instance rowFrameNormed (m N : ℕ) : NormedAddCommGroup
    (EuclideanSpace ℝ {p : Fin m × Fin m // p.1 ≤ p.2} →L[ℝ]
      EuclideanSpace ℝ (Fin N)) := inferInstance
private local instance rowFrameSpace (m N : ℕ) : NormedSpace ℝ
    (EuclideanSpace ℝ {p : Fin m × Fin m // p.1 ≤ p.2} →L[ℝ]
      EuclideanSpace ℝ (Fin N)) := inferInstance

def actualNormalChartTransferCost (T : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (j+1), actualFastTensorChartTransferCost T k

theorem actualFastTensorChartTransferCost_nonneg (T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i) (j : ℕ) :
    0 ≤ actualFastTensorChartTransferCost T j := by
  unfold actualFastTensorChartTransferCost
  exact mul_nonneg (mul_nonneg (by positivity) (actualFastChartTransferPrefix_nonneg T hT j))
    (sq_nonneg _)

theorem actualNormalChartTransferCost_nonneg (T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i) (j : ℕ) :
    0 ≤ actualNormalChartTransferCost T j :=
  Finset.sum_nonneg (fun k _ => actualFastTensorChartTransferCost_nonneg T hT k)

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

theorem actual_normal_hessian_transferred_from_original_jets
    (T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i) (j : ℕ)
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (e0 e1 : Ep → OpenPartialHomeomorph M D)
    (he0 : ∀ p, e0 p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (U W : Set X) (hU : IsOpen U) (hW : IsOpen W)
    (hcoord0 : ∀ z ∈ W, z.2 ∈ (e0 z.1).target)
    (hF0 : ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e0 z.1).symm z.2)) W)
    (hA0 : ContDiffOn ℝ ∞ (fun z : X => fderiv ℝ (F z.1 ∘ (e0 z.1).symm) z.2) W)
    (hH0 : ContDiffOn ℝ ∞ (fun z : X => fderiv ℝ (fderiv ℝ (F z.1 ∘ (e0 z.1).symm)) z.2) W)
    (hphi : ContDiffOn ℝ ∞ (actualSourceChartTransition e0 e1) U)
    (hmap : MapsTo (actualSourceChartTransition e0 e1) U W)
    (hcoord : ∀ z ∈ U, z.2 ∈ (e1 z.1).target ∧ (e1 z.1).symm z.2 ∈ (e0 z.1).source)
    (ell c MA MH : ℝ) (hell : 0 < ell) (hc : 0 < c) (hMA : 0 ≤ MA) (hMH : 0 ≤ MH)
    (hreserve : ∀ z ∈ W, ∀ v : D, c*‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e0 z.1).symm) z.2 v‖^2)
    (hAj : ∀ k ≤ j, ∀ z ∈ W, ell^k*‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (F y.1 ∘ (e0 y.1).symm) y.2) z‖ ≤ MA)
    (hHj : ∀ k ≤ j, ∀ z ∈ W, ell^k*‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (fderiv ℝ (F y.1 ∘ (e0 y.1).symm)) y.2) z‖ ≤ MH)
    (hphijet : ∀ k, 1 ≤ k → k ≤ j+1 → ∀ z ∈ U,
      ell^(k-1)*‖iteratedFDeriv ℝ k (actualSourceChartTransition e0 e1) z‖ ≤ T k) :
    ContDiffOn ℝ ∞ (actualNormalHessianInChart F e1) U ∧
    ∀ k ≤ j, ∀ z ∈ U, ell^k*‖iteratedFDeriv ℝ k (actualNormalHessianInChart F e1) z‖ ≤
      actualNormalChartTransferCost T j * actualIncrementSecondFormConstant m N j c MA MH := by
  let Q0 := actualNormalHessianInChart F e0
  let phi := actualSourceChartTransition e0 e1
  let R : X → D →L[ℝ] D →L[ℝ] V := fun z => (Q0 (phi z)).bilinearComp
    (actualJointSpatialJacobian phi z) (actualJointSpatialJacobian phi z)
  let K := actualIncrementSecondFormConstant m N j c MA MH
  have hK : 0 ≤ K := actualIncrementSecondFormConstant_nonneg m N j hc hMA hMH
  obtain ⟨hQ0,hQ0b⟩ := actual_increment_projected_hessian_slow_jets F hF e0 he0 W hW
    hcoord0 hA0 hH0 j ell c MA MH hell hc hMA hMH hreserve hAj hHj
  change ContDiffOn ℝ ∞ Q0 W at hQ0
  have hR (k : ℕ) (hk : k ≤ j) (z : X) (hz : z ∈ U) :
      ContDiffOn ℝ ∞ R U ∧ ell^k*‖iteratedFDeriv ℝ k R z‖ ≤
        actualFastTensorChartTransferCost T k*K := by
    exact actual_fast_joint_tensor_chart_transfer T hT k phi Q0 U W hU hW hphi hQ0 hmap
      z hz ell ell K hell le_rfl hK
      (fun i hi => hQ0b i (hi.trans hk) (phi z) (hmap hz))
      (fun i hi hik => hphijet i hi (by omega) z hz)
  have hRsm : ContDiffOn ℝ ∞ R U := by
    by_cases hne : U.Nonempty
    · obtain ⟨z,hz⟩ := hne
      exact (hR 0 (by omega) z hz).1
    · have hE : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      simp [hE]
  have heq : EqOn (actualNormalHessianInChart F e1) R U :=
    fun z hz => actual_normal_hessian_true_chart_transition F hF e0 e1 he0 U W hU hW
      hF0 hphi hmap hcoord z hz
  refine ⟨hRsm.congr heq,?_⟩
  intro k hk z hz
  have hg : actualNormalHessianInChart F e1 =ᶠ[𝓝 z] R :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hz) (fun y hy => heq hy)
  rw [(hg.iteratedFDeriv ℝ k).eq_of_nhds]
  apply (hR k hk z hz).2.trans
  apply mul_le_mul_of_nonneg_right _ hK
  exact Finset.single_le_sum (fun i _ => actualFastTensorChartTransferCost_nonneg T hT i)
    (by simpa using hk)

/-- The SAME canonical true-B rows and transverse frame are fixed linear
observations of the transported normal Hessian, so no extra inverse-chart
Hessian loss appears in their slow profiles. -/
theorem actual_true_geometry_from_normal_hessian_profile
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (e : Ep → OpenPartialHomeomorph M D)
    (he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (U : Set X) (hU : IsOpen U) (hcoord : ∀ z ∈ U, z.2 ∈ (e z.1).target)
    (hQ : ContDiffOn ℝ ∞ (actualNormalHessianInChart F e) U)
    (j : ℕ) (ell K : ℝ) (hell : 0 ≤ ell)
    (hQj : ∀ k ≤ j, ∀ z ∈ U,
      ell^k*‖iteratedFDeriv ℝ k (actualNormalHessianInChart F e) z‖ ≤ K) :
    (ContDiffOn ℝ ∞ (fun z : X => fun i : Fin (m+1) =>
      (incrementsModeSecondForm (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2 0 i : V)) U ∧
      ∀ k ≤ j, ∀ z ∈ U, ell^k*‖iteratedFDeriv ℝ k (fun y : X => fun i : Fin (m+1) =>
        (incrementsModeSecondForm (I := 𝓙) (F y.1) (hF y.1) (e y.1).symm y.2 0 i : V)) z‖ ≤
          ‖actualIncrementFirstRows m N‖*K) ∧
    (ContDiffOn ℝ ∞ (fun z : X => incrementsModeAmbientTransverseFrame (I := 𝓙)
      (F z.1) (hF z.1) (e z.1).symm z.2) U ∧
      ∀ k ≤ j, ∀ z ∈ U, ell^k*‖iteratedFDeriv ℝ k (fun y : X =>
        incrementsModeAmbientTransverseFrame (I := 𝓙) (F y.1) (hF y.1) (e y.1).symm y.2) z‖ ≤
          ‖actualIncrementTransverseColumns m N‖*K) := by
  let Q := actualNormalHessianInChart F e
  have hrow : ∀ z ∈ U, (fun i : Fin (m+1) =>
      (incrementsModeSecondForm (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2 0 i : V)) =
        actualIncrementFirstRows m N (Q z) := by
    intro z hz
    funext i
    exact actual_increment_secondForm_chart (F z.1) (hF z.1) (e z.1) (he z.1) z.2 (hcoord z hz) 0 i
  have hcol : ∀ z ∈ U, incrementsModeAmbientTransverseFrame (I := 𝓙)
      (F z.1) (hF z.1) (e z.1).symm z.2 = actualIncrementTransverseColumns m N (Q z) := by
    intro z hz
    rw [actualIncrementTransverseColumns_apply]
    unfold incrementsModeAmbientTransverseFrame
    apply Finset.sum_congr rfl
    intro q _
    exact congrArg (fun v : V => (EuclideanSpace.proj q).smulRight v)
      (actual_increment_secondForm_chart (F z.1) (hF z.1) (e z.1) (he z.1) z.2 (hcoord z hz)
        q.val.1.succ q.val.2.succ)
  constructor
  · refine ⟨((actualIncrementFirstRows m N).contDiff.comp_contDiffOn hQ).congr hrow,?_⟩
    intro k hk z hz
    have hg := Filter.eventuallyEq_of_mem (hU.mem_nhds hz) (fun y hy => hrow y hy)
    rw [(hg.iteratedFDeriv ℝ k).eq_of_nhds]
    exact slow_linear_jet_bound (actualIncrementFirstRows m N) U hU Q hQ k ell K hell z hz (hQj k hk z hz)
  · refine ⟨((actualIncrementTransverseColumns m N).contDiff.comp_contDiffOn hQ).congr hcol,?_⟩
    intro k hk z hz
    have hg := Filter.eventuallyEq_of_mem (hU.mem_nhds hz) (fun y hy => hcol y hy)
    rw [(hg.iteratedFDeriv ℝ k).eq_of_nhds]
    exact slow_linear_jet_bound (actualIncrementTransverseColumns m N) U hU Q hQ k ell K hell z hz (hQj k hk z hz)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_normal_hessian_transferred_from_original_jets
#print axioms GlobalEmbedding.Continuation.actual_true_geometry_from_normal_hessian_profile
