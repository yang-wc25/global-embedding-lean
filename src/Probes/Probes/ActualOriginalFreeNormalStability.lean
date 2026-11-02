import Probes.ActualFreeNormalProjectionStability
import Probes.ActualOriginalTransverseStability
import Probes.ActualOriginalUnitFreeNormalLegal

/-! The actual unit free normal keeps a quantitative normalization reserve
under a genuine two-jet perturbation of the SAME map in the SAME chart. The
first/transverse frames and their differences are internally the actual
derivatives and projected Hessian columns. No candidate-frame or new-normal
reserve is an input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
private local instance nfFirstNormed : NormedAddCommGroup (D →L[ℝ] V) := inferInstance
private local instance nfFirstSpace : NormedSpace ℝ (D →L[ℝ] V) := inferInstance
private local instance nfHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance nfHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance nfFrameNormed : NormedAddCommGroup (Tdata →L[ℝ] V) := inferInstance
private local instance nfFrameSpace : NormedSpace ℝ (Tdata →L[ℝ] V) := inferInstance
private local instance nfColumnsNormed : NormedAddCommGroup
    ((D →L[ℝ] D →L[ℝ] V) →L[ℝ] Tdata →L[ℝ] V) := ContinuousLinearMap.toNormedAddCommGroup
private local instance nfColumnsSpace : NormedSpace ℝ
    ((D →L[ℝ] D →L[ℝ] V) →L[ℝ] Tdata →L[ℝ] V) := ContinuousLinearMap.toNormedSpace

theorem actual_original_frame_orthogonal_of_normal_beta
    (F : M → V) (hF : ContMDiff 𝓙 𝓘(ℝ,V) ∞ F) (c : D → M) (x : D)
    (v : normalSpace (I := 𝓙) F (c x))
    (hbeta : incrementsTransversePairing F hF (c x)
      (fun a : Fin m => incrementsModeCoordinateDirections c x a.succ) v = 0) :
    (v : V) ∈ (LinearMap.range (incrementsModeAmbientTransverseFrame F hF c x).toLinearMap)ᗮ := by
  let beta := incrementsTransversePairing F hF (c x)
    (fun a : Fin m => incrementsModeCoordinateDirections c x a.succ)
  apply (Submodule.mem_orthogonal _ _).mpr
  rintro w ⟨t,rfl⟩
  have he := congrArg (fun L : Tdata →L[ℝ] V => L t)
    (incrementsModeAmbientTransverseFrame_eq F hF c x)
  change incrementsModeAmbientTransverseFrame F hF c x t = (beta.adjoint t : V) at he
  change inner ℝ (incrementsModeAmbientTransverseFrame F hF c x t) (v : V) = 0
  rw [he]
  change inner ℝ (beta.adjoint t) v = 0
  rw [beta.adjoint_inner_left]
  change inner ℝ t (beta v) = 0
  rw [hbeta,inner_zero_right]

theorem actual_original_two_jet_free_normal_reserve
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
      ∀ (normal : normalSpace (I := 𝓙) F0 (e.symm x)), ‖normal‖ = 1 →
      incrementsTransversePairing F0 hF0 (e.symm x)
        (fun a : Fin m => incrementsModeCoordinateDirections e.symm x a.succ) normal = 0 →
      (∀ v : D, (cF/4)*‖v‖^2 ≤ ‖fderiv ℝ (F ∘ e.symm) x v‖^2) ∧
      (∀ v : Tdata, (cT/4)*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame F hF e.symm x v‖^2) ∧
      (1/2 : ℝ) ≤ ‖actualFreeNormalProjectionRaw
        (fderiv ℝ (F ∘ e.symm) x)
        (incrementsModeAmbientTransverseFrame F hF e.symm x) (normal : V)‖ := by
  obtain ⟨eg,heg,hgeom⟩ := actual_original_selected_frame_uniform_stability
    (m := m) (N := N) (M := M) cF cT MH hcF hcT hMH
  obtain ⟨en,hen,hnormal⟩ := actual_free_normal_projection_uniform_reserve
    (E := D) (T := Tdata) (N := N) cF cT hcF hcT
  let C := ‖actualIncrementTransverseColumns m N‖*(1+(3/Real.sqrt cF)*MH)
  have hC : 0 ≤ C := mul_nonneg (norm_nonneg _) (by positivity)
  let epsilon := min eg (min (Real.sqrt cF/2) (min en (en/(C+1))))
  have hepsilon : 0 < epsilon := lt_min heg (lt_min (by positivity) (lt_min hen (by positivity)))
  have heg' : epsilon ≤ eg := min_le_left _ _
  have hesmall : epsilon ≤ Real.sqrt cF/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hen' : epsilon ≤ en := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hCost : C*epsilon ≤ en := by
    calc
      _ ≤ C*(en/(C+1)) := mul_le_mul_of_nonneg_left
        (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)) hC
      _ ≤ (C+1)*(en/(C+1)) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = en := by field_simp
  refine ⟨epsilon,hepsilon,?_⟩
  intro F0 F hF0 hF e he x hx hFirst hTransverse hHessian hD hH normal hUnit hBeta
  obtain ⟨hNewFirst,hNewTransverse⟩ := hgeom F0 F hF0 hF e he x hx hFirst hTransverse
    hHessian (hD.trans heg') (hH.trans heg')
  refine ⟨hNewFirst,hNewTransverse,?_⟩
  have hFrame := actual_original_transverse_frame_two_jet_difference F0 F hF0 hF e he x hx
    cF MH hcF hFirst hHessian (hD.trans hesmall)
  have hFrameSmall : ‖incrementsModeAmbientTransverseFrame F0 hF0 e.symm x-
      incrementsModeAmbientTransverseFrame F hF e.symm x‖ ≤ en := by
    rw [norm_sub_rev]
    apply (hFrame.trans ?_).trans hCost
    calc
      _ ≤ ‖actualIncrementTransverseColumns m N‖*(epsilon+(3/Real.sqrt cF)*MH*epsilon) :=
        mul_le_mul_of_nonneg_left
          (add_le_add hH (mul_le_mul_of_nonneg_left hD (by positivity))) (norm_nonneg _)
      _ = C*epsilon := by dsimp [C]; ring
  apply hnormal _ _ _ _ hFirst hTransverse (hD.trans hen') hFrameSmall (normal : V) hUnit
  · rw [← actual_increment_normalSpace_eq_chart_range F0 hF0 e he x hx]
    exact normal.property
  · exact actual_original_frame_orthogonal_of_normal_beta F0 hF0 e.symm x normal hBeta

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_frame_orthogonal_of_normal_beta
#print axioms GlobalEmbedding.Continuation.actual_original_two_jet_free_normal_reserve
