import Probes.ActualIncrementTrueBJets
import Probes.ActualFirstFramePerturbation
import GlobalEmbedding.Paper.PointwiseJetNormalBound

/-!
# The same selected transverse frame persists under actual two-jet changes

The first jet and Hessian are the derivatives of the two displayed maps in
the SAME actual chart. The true normal columns are identified with the
projected Hessian columns, so no independent candidate frame is an input.
The tolerance depends only on the fixed reference reserves and Hessian
budget, and is chosen before the perturbing map. No tangent Riemannian
bundle, chosen inverse estimate, or all-order profile is used.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Function
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

variable {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
local notation "𝓙" => 𝓘(ℝ,D)
private local instance stabilityFirstNormed : NormedAddCommGroup (D →L[ℝ] V) := inferInstance
private local instance stabilityFirstSpace : NormedSpace ℝ (D →L[ℝ] V) := inferInstance
private local instance stabilityHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance stabilityHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance stabilityFrameNormed : NormedAddCommGroup (Tdata →L[ℝ] V) := inferInstance
private local instance stabilityFrameSpace : NormedSpace ℝ (Tdata →L[ℝ] V) := inferInstance
private local instance stabilityColumnsNormed : NormedAddCommGroup
    ((D →L[ℝ] D →L[ℝ] V) →L[ℝ] Tdata →L[ℝ] V) := ContinuousLinearMap.toNormedAddCommGroup
private local instance stabilityColumnsSpace : NormedSpace ℝ
    ((D →L[ℝ] D →L[ℝ] V) →L[ℝ] Tdata →L[ℝ] V) := ContinuousLinearMap.toNormedSpace
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

theorem actual_original_transverse_frame_projected_columns
    (F : M → V) (hF : ContMDiff 𝓙 𝓘(ℝ,V) ∞ F)
    (e : OpenPartialHomeomorph M D) (he : e ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (x : D) (hx : x ∈ e.target) :
    incrementsModeAmbientTransverseFrame F hF e.symm x =
      (LinearMap.range (fderiv ℝ (F ∘ e.symm) x).toLinearMap)ᗮ.starProjection.comp
        (actualIncrementTransverseColumns m N (fderiv ℝ (fderiv ℝ (F ∘ e.symm)) x)) := by
  have hproj : (normalSpace (I := 𝓙) F (e.symm x)).starProjection =
      (LinearMap.range (fderiv ℝ (F ∘ e.symm) x).toLinearMap)ᗮ.starProjection := by
    rw [actual_increment_normalSpace_eq_chart_range F hF e he x hx]
  rw [← hproj,actualIncrementTransverseColumns_apply]
  apply ContinuousLinearMap.ext
  intro t
  simp only [incrementsModeAmbientTransverseFrame,sum_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.comp_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro q hq
  exact congrArg (fun v : V => (EuclideanSpace.proj q t) • v)
    (actual_increment_secondForm_chart F hF e he x hx q.val.1.succ q.val.2.succ)

theorem actual_original_transverse_frame_two_jet_difference
    (F0 F : M → V) (hF0 : ContMDiff 𝓙 𝓘(ℝ,V) ∞ F0)
    (hF : ContMDiff 𝓙 𝓘(ℝ,V) ∞ F)
    (e : OpenPartialHomeomorph M D) (he : e ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (x : D) (hx : x ∈ e.target) (cF MH : ℝ) (hcF : 0 < cF)
    (hFirst : ∀ v : D, cF*‖v‖^2 ≤ ‖fderiv ℝ (F0 ∘ e.symm) x v‖^2)
    (hHessian : ‖fderiv ℝ (fderiv ℝ (F0 ∘ e.symm)) x‖ ≤ MH)
    (hSmall : ‖fderiv ℝ (F0 ∘ e.symm) x-fderiv ℝ (F ∘ e.symm) x‖ ≤ Real.sqrt cF/2) :
    ‖incrementsModeAmbientTransverseFrame F hF e.symm x-
        incrementsModeAmbientTransverseFrame F0 hF0 e.symm x‖ ≤
      ‖actualIncrementTransverseColumns m N‖ *
        (‖fderiv ℝ (fderiv ℝ (F ∘ e.symm)) x-fderiv ℝ (fderiv ℝ (F0 ∘ e.symm)) x‖ +
          (3/Real.sqrt cF)*MH*‖fderiv ℝ (F0 ∘ e.symm) x-fderiv ℝ (F ∘ e.symm) x‖) := by
  let A0 := fderiv ℝ (F0 ∘ e.symm) x
  let A := fderiv ℝ (F ∘ e.symm) x
  let H0 := fderiv ℝ (fderiv ℝ (F0 ∘ e.symm)) x
  let H := fderiv ℝ (fderiv ℝ (F ∘ e.symm)) x
  let L := actualIncrementTransverseColumns m N
  have hQ : ‖L H0‖ ≤ ‖L‖*MH :=
    (L.le_opNorm H0).trans (mul_le_mul_of_nonneg_left hHessian (norm_nonneg L))
  have hQdiff : ‖L H-L H0‖ ≤ ‖L‖*‖H-H0‖ := by
    rw [← map_sub]
    exact L.le_opNorm (H-H0)
  have h := (pointwise_projected_jet_estimate A0 A (L H0) (L H)
    cF (‖L‖*MH) hcF hFirst hSmall hQ).2
  rw [actual_original_transverse_frame_projected_columns F hF e he x hx,
    actual_original_transverse_frame_projected_columns F0 hF0 e he x hx]
  apply h.trans
  calc
    _ ≤ ‖L‖*‖H-H0‖+(3/Real.sqrt cF)*(‖L‖*MH)*‖A0-A‖ :=
      add_le_add hQdiff le_rfl
    _ = _ := by ring

/-- A reference selected packet keeps both reserves for every sufficiently
close actual map. The tolerance is independent of the map, point and chart. -/
theorem actual_original_selected_frame_uniform_stability
    (cF cT MH : ℝ) (hcF : 0 < cF) (hcT : 0 < cT) (hMH : 0 ≤ MH) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀
      (F0 F : M → V) (hF0 : ContMDiff 𝓙 𝓘(ℝ,V) ∞ F0)
      (hF : ContMDiff 𝓙 𝓘(ℝ,V) ∞ F)
      (e : OpenPartialHomeomorph M D) (_he : e ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
      (x : D), x ∈ e.target →
      (∀ v : D, cF*‖v‖^2 ≤ ‖fderiv ℝ (F0 ∘ e.symm) x v‖^2) →
      (∀ v : Tdata, cT*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame F0 hF0 e.symm x v‖^2) →
      ‖fderiv ℝ (fderiv ℝ (F0 ∘ e.symm)) x‖ ≤ MH →
      ‖fderiv ℝ (F0 ∘ e.symm) x-fderiv ℝ (F ∘ e.symm) x‖ ≤ epsilon →
      ‖fderiv ℝ (fderiv ℝ (F ∘ e.symm)) x-fderiv ℝ (fderiv ℝ (F0 ∘ e.symm)) x‖ ≤ epsilon →
      (∀ v : D, (cF/4)*‖v‖^2 ≤ ‖fderiv ℝ (F ∘ e.symm) x v‖^2) ∧
      (∀ v : Tdata, (cT/4)*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame F hF e.symm x v‖^2) := by
  let L := actualIncrementTransverseColumns m N
  let C := ‖L‖*(1+(3/Real.sqrt cF)*MH)
  have hC : 0 ≤ C := mul_nonneg (norm_nonneg L) (by positivity)
  let epsilon := min (Real.sqrt cF/2) (Real.sqrt cT/(2*(C+1)))
  have hepsilon : 0 < epsilon := lt_min (by positivity) (by positivity)
  have hsmallF : epsilon ≤ Real.sqrt cF/2 := min_le_left _ _
  have hsmallT : C*epsilon ≤ Real.sqrt cT/2 := by
    calc
      _ ≤ C*(Real.sqrt cT/(2*(C+1))) := mul_le_mul_of_nonneg_left (min_le_right _ _) hC
      _ ≤ (C+1)*(Real.sqrt cT/(2*(C+1))) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = Real.sqrt cT/2 := by field_simp
  refine ⟨epsilon,hepsilon,?_⟩
  intro F0 F hF0 hF e he x hx hFirst hTransverse hHessian hD hH
  have hframe := actual_original_transverse_frame_two_jet_difference F0 F hF0 hF e he x hx
    cF MH hcF hFirst hHessian (hD.trans hsmallF)
  have hframeSmall : ‖incrementsModeAmbientTransverseFrame F hF e.symm x-
      incrementsModeAmbientTransverseFrame F0 hF0 e.symm x‖ ≤ Real.sqrt cT/2 := by
    apply (hframe.trans ?_).trans hsmallT
    calc
      _ ≤ ‖L‖*(epsilon+(3/Real.sqrt cF)*MH*epsilon) :=
        mul_le_mul_of_nonneg_left
          (add_le_add hH (mul_le_mul_of_nonneg_left hD (by positivity))) (norm_nonneg L)
      _ = C*epsilon := by ring
  exact ⟨actual_first_frame_reserve_perturbation _ _ cF hcF hFirst
    (by simpa only [norm_sub_rev] using hD.trans hsmallF),
    actual_first_frame_reserve_perturbation _ _ cT hcT hTransverse hframeSmall⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_original_transverse_frame_projected_columns
#print axioms GlobalEmbedding.Continuation.actual_original_transverse_frame_two_jet_difference
#print axioms GlobalEmbedding.Continuation.actual_original_selected_frame_uniform_stability
