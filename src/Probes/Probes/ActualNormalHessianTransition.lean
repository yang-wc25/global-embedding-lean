import Probes.ActualIncrementHessianJets
import Probes.ActualJointTensorChartTransfer
import GlobalEmbedding.Paper.ProjectedHessianChain

/-!
# The actual normal Hessian is a true tensor under chosen chart transitions

The ordinary coordinate Hessian contains a second derivative of the transition.
The original normal projection kills that term because it is in the actual
first-derivative range. The resulting identity retains both true spatial
Jacobian factors, in all parameter-dependent charts.
-/

noncomputable section
open GlobalEmbedding.Paper Manifold Set Function Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

def actualNormalHessianInChart (F : Ep → M → V)
    (e : Ep → OpenPartialHomeomorph M D) (z : X) : D →L[ℝ] D →L[ℝ] V :=
  actualIncrementPostcomposeHessian D V
    (normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2)).starProjection
    (fderiv ℝ (fderiv ℝ (F z.1 ∘ (e z.1).symm)) z.2)

def actualSourceChartTransition (e0 e1 : Ep → OpenPartialHomeomorph M D) (z : X) : X :=
  (z.1,e0 z.1 ((e1 z.1).symm z.2))

theorem actual_normal_hessian_true_chart_transition
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (e0 e1 : Ep → OpenPartialHomeomorph M D)
    (he0 : ∀ p, e0 p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (U W : Set X) (hU : IsOpen U) (hW : IsOpen W)
    (hF0 : ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e0 z.1).symm z.2)) W)
    (hphi : ContDiffOn ℝ ∞ (actualSourceChartTransition e0 e1) U)
    (hmap : MapsTo (actualSourceChartTransition e0 e1) U W)
    (hcoord : ∀ z ∈ U, z.2 ∈ (e1 z.1).target ∧ (e1 z.1).symm z.2 ∈ (e0 z.1).source)
    (z : X) (hz : z ∈ U) :
    actualNormalHessianInChart F e1 z =
      (actualNormalHessianInChart F e0 (actualSourceChartTransition e0 e1 z)).bilinearComp
        (actualJointSpatialJacobian (actualSourceChartTransition e0 e1) z)
        (actualJointSpatialJacobian (actualSourceChartTransition e0 e1) z) := by
  let phi := actualSourceChartTransition e0 e1
  let f0 := F z.1 ∘ (e0 z.1).symm
  let f1 := F z.1 ∘ (e1 z.1).symm
  let t : D → D := fun x => e0 z.1 ((e1 z.1).symm x)
  have htx : (e0 z.1).symm (t z.2) = (e1 z.1).symm z.2 :=
    (e0 z.1).left_inv (hcoord z hz).2
  have hf0 : ContDiffAt ℝ 2 f0 (t z.2) := by
    have h := (hF0.contDiffAt (hW.mem_nhds (hmap hz))).comp (t z.2)
      (contDiffAt_const.prodMk contDiffAt_id)
    exact h.of_le (by simp)
  have ht : ContDiffAt ℝ 2 t z.2 := by
    have h := (hphi.snd.contDiffAt (hU.mem_nhds hz)).comp z.2
      (contDiffAt_const.prodMk contDiffAt_id)
    exact h.of_le (by simp)
  have heq : f1 =ᶠ[𝓝 z.2] f0 ∘ t := by
    filter_upwards [(hU.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz] with x hx
    change F z.1 ((e1 z.1).symm x) = F z.1 ((e0 z.1).symm (e0 z.1 ((e1 z.1).symm x)))
    rw [(e0 z.1).left_inv (hcoord (z.1,x) hx).2]
  let P := (normalSpace (I := 𝓙) (F z.1) ((e1 z.1).symm z.2)).starProjection
  have hP : ∀ v : D, P (fderiv ℝ f0 (t z.2) v) = 0 := by
    intro v
    have htarget : t z.2 ∈ (e0 z.1).target := (e0 z.1).map_source (hcoord z hz).2
    have hnormal := actual_increment_normalSpace_eq_chart_range (F z.1) (hF z.1)
      (e0 z.1) (he0 z.1) (t z.2) htarget
    rw [htx] at hnormal
    change (normalSpace (I := 𝓙) (F z.1) ((e1 z.1).symm z.2)).starProjection
      (fderiv ℝ f0 (t z.2) v) = 0
    rw [hnormal,Submodule.starProjection_apply_eq_zero_iff]
    exact (LinearMap.range (fderiv ℝ f0 (t z.2)).toLinearMap).le_orthogonal_orthogonal ⟨v,rfl⟩
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  change P (fderiv ℝ (fderiv ℝ f1) z.2 v w) =
    (normalSpace (I := 𝓙) (F z.1) ((e0 z.1).symm (t z.2))).starProjection
      (fderiv ℝ (fderiv ℝ f0) (t z.2) (fderiv ℝ t z.2 v) (fderiv ℝ t z.2 w))
  rw [htx,heq.fderiv.fderiv_eq]
  exact projected_hessian_chain f0 t P z.2 hf0 ht hP v w

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_normal_hessian_true_chart_transition
