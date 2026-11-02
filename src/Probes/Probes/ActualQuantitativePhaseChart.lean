import Probes.ActualQuantitativePhaseLinear

/-!
# A quantitative chart for the literal phase, preserving every parameter

The source is exactly the prescribed ball. The inverse has an explicit native
Lipschitz bound, the target contains an explicit ball, and both maps are smooth.
The sole differential input is a bound on the original phase differential's
oscillation, together with its actual nonzero distinguished spatial derivative.
-/

noncomputable section
open Set Function Metric
open scoped ContDiff Topology NNReal
namespace GlobalEmbedding.Continuation

variable {Ep Et : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [CompleteSpace Ep]
  [NormedAddCommGroup Et] [NormedSpace ℝ Et] [CompleteSpace Et]

def actualPhaseCoordinateMap (psi : Ep × (ℝ × Et) → ℝ) (z : Ep × (ℝ × Et)) :
    Ep × (ℝ × Et) := (z.1,(psi z,z.2.2))

omit [CompleteSpace Ep] [CompleteSpace Et] in
theorem actual_phase_coordinate_hasFDerivAt
    (psi : Ep × (ℝ × Et) → ℝ) (z : Ep × (ℝ × Et))
    (hpsi : DifferentiableAt ℝ psi z) :
    HasFDerivAt (actualPhaseCoordinateMap psi)
      (actualPhaseTriangular (fderiv ℝ psi z)) z := by
  let L := (ContinuousLinearMap.snd ℝ ℝ Et).comp
    (ContinuousLinearMap.snd ℝ Ep (ℝ × Et))
  exact (ContinuousLinearMap.fst ℝ Ep (ℝ × Et)).hasFDerivAt.prodMk
    (hpsi.hasFDerivAt.prodMk L.hasFDerivAt)

theorem actual_quantitative_phase_chart_of_oscillation
    (psi : Ep × (ℝ × Et) → ℝ) (z0 : Ep × (ℝ × Et)) (r : ℝ) (hr : 0 < r)
    (hpsi : ContDiffOn ℝ ∞ psi (ball z0 r))
    (ha : fderiv ℝ psi z0 (0,(1,0)) ≠ 0) (c : ℝ≥0)
    (hcaxis : (c:ℝ) < |fderiv ℝ psi z0 (0,(1,0))|)
    (hc : c < ‖((actualPhaseTriangularEquiv (fderiv ℝ psi z0) ha).symm :
      (Ep × (ℝ × Et)) →L[ℝ] (Ep × (ℝ × Et)))‖₊⁻¹)
    (hosc : ∀ z ∈ ball z0 r, ‖fderiv ℝ psi z-fderiv ℝ psi z0‖ ≤ c) :
    ∃ a : OpenPartialHomeomorph (Ep × (ℝ × Et)) (Ep × (ℝ × Et)),
      a.source = ball z0 r ∧ (a : (Ep × (ℝ × Et)) → (Ep × (ℝ × Et))) =
        actualPhaseCoordinateMap psi ∧
      ContDiffOn ℝ ∞ a a.source ∧ ContDiffOn ℝ ∞ a.symm a.target ∧
      (∀ z ∈ a.target, (a.symm z).1 = z.1 ∧ psi (a.symm z) = z.2.1) ∧
      LipschitzOnWith
        ((‖((actualPhaseTriangularEquiv (fderiv ℝ psi z0) ha).symm :
          (Ep × (ℝ × Et)) →L[ℝ] (Ep × (ℝ × Et)))‖₊⁻¹-c)⁻¹) a.symm a.target ∧
      (∀ y ∈ a.target, ‖fderiv ℝ a.symm y‖ ≤
        ((‖((actualPhaseTriangularEquiv (fderiv ℝ psi z0) ha).symm :
          (Ep × (ℝ × Et)) →L[ℝ] (Ep × (ℝ × Et)))‖₊⁻¹-c)⁻¹ : ℝ≥0)) ∧
      closedBall (actualPhaseCoordinateMap psi z0)
        ((‖((actualPhaseTriangularEquiv (fderiv ℝ psi z0) ha).symm :
          (Ep × (ℝ × Et)) →L[ℝ] (Ep × (ℝ × Et)))‖₊⁻¹-c : ℝ≥0)*(r/2)) ⊆ a.target := by
  let T := actualPhaseCoordinateMap psi
  let L := actualPhaseTriangularEquiv (fderiv ℝ psi z0) ha
  have hD (z) (hz : z ∈ ball z0 r) :=
    (hpsi.contDiffAt (isOpen_ball.mem_nhds hz)).differentiableAt (by simp)
  have hT : ContDiffOn ℝ ∞ T (ball z0 r) :=
    contDiffOn_fst.prodMk (hpsi.prodMk contDiffOn_snd.snd)
  have hTd (z) (hz : z ∈ ball z0 r) :
      HasFDerivAt T (actualPhaseTriangular (fderiv ℝ psi z)) z :=
    actual_phase_coordinate_hasFDerivAt psi z (hD z hz)
  have happ : ApproximatesLinearOn T (L : _ →L[ℝ] _) (ball z0 r) c := by
    intro x hx y hy
    apply (convex_ball z0 r).norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (fun z hz => (hTd z hz).hasFDerivWithinAt) _ hy hx
    intro z hz
    exact (actual_phase_triangular_difference_bound _ _).trans (hosc z hz)
  let a := happ.toOpenPartialHomeomorph T (ball z0 r) (Or.inr hc) isOpen_ball
  have hfun : (a : (Ep × (ℝ × Et)) → (Ep × (ℝ × Et))) = T := rfl
  have hsource : a.source = ball z0 r := rfl
  have hpoint (z) (hz : z ∈ ball z0 r) : fderiv ℝ psi z (0,(1,0)) ≠ 0 := by
    have he := (fderiv ℝ psi z-fderiv ℝ psi z0).le_opNorm (0,(1,0))
    have hb : |fderiv ℝ psi z (0,(1,0))-fderiv ℝ psi z0 (0,(1,0))| ≤ (c:ℝ) := by
      simpa using he.trans (mul_le_mul_of_nonneg_right (hosc z hz) (norm_nonneg _))
    intro hzero
    rw [hzero,zero_sub,abs_neg] at hb
    exact (not_le.mpr hcaxis) hb
  have hinv : ContDiffOn ℝ ∞ a.symm a.target := by
    intro y hy
    have hx : a.symm y ∈ ball z0 r := a.map_target hy
    let e := actualPhaseTriangularEquiv (fderiv ℝ psi (a.symm y)) (hpoint _ hx)
    have hd : HasFDerivAt a (e : _ →L[ℝ] _) (a.symm y) := hTd _ hx
    exact (a.contDiffAt_symm hy hd (hT.contDiffAt (isOpen_ball.mem_nhds hx))).contDiffWithinAt
  have hidentity (z) (hz : z ∈ a.target) :
      (a.symm z).1 = z.1 ∧ psi (a.symm z) = z.2.1 := by
    have he : T (a.symm z) = z := a.right_inv hz
    have hf := congrArg Prod.fst he
    have hp := congrArg (fun w => w.2.1) he
    exact ⟨hf,hp⟩
  have hlip : LipschitzOnWith
      ((‖(L.symm : (Ep × (ℝ × Et)) →L[ℝ] (Ep × (ℝ × Et)))‖₊⁻¹-c)⁻¹)
      a.symm a.target := by
    apply LipschitzOnWith.of_dist_le_mul
    intro y hy z hz
    have h := (happ.antilipschitzWith (Or.inr hc)).le_mul_dist
      ⟨a.symm y,a.map_target hy⟩ ⟨a.symm z,a.map_target hz⟩
    change dist (a.symm y) (a.symm z) ≤ _*dist (a (a.symm y)) (a (a.symm z)) at h
    simpa only [a.right_inv hy,a.right_inv hz] using h
  refine ⟨a,hsource,hfun,hT,hinv,hidentity,hlip,?_,?_⟩
  · intro y hy
    exact norm_fderiv_le_of_lipschitzOn ℝ (a.open_target.mem_nhds hy) hlip
  · rw [NNReal.coe_sub hc.le]
    apply happ.closedBall_subset_target (Or.inr hc) isOpen_ball (by positivity)
    exact closedBall_subset_ball (by linarith)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_quantitative_phase_chart_of_oscillation
