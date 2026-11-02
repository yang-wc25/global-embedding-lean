import Probes.ActualOriginalFreeNormalField

/-! The actual two-projection construction with a varying reference field.
The reference field's original slow profile is consumed by the genuine
bilinear evaluation. All new-normal profiles are produced, not supplied.
Named constants depend only on finite scalar budgets and positive reserves.
Both abstract projection and actual manifold field use these same constants. -/

noncomputable section
open GlobalEmbedding.Paper Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {N : ℕ} {E T : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- A fixed finite-dimensional normalization operation on the annulus
mu <= norm(v) <= Mraw. Its choice is over numeric data, before any field. -/
def round4UnitNormalizationConstant (N j : ℕ) (mu Mraw : ℝ) (hmu : 0 < mu) : ℝ :=
  Classical.choose (actual_unit_normalization_slow_jets.{0} (N := N) j mu Mraw hmu)

theorem round4UnitNormalizationConstant_nonneg (N j : ℕ) (mu Mraw : ℝ) (hmu : 0 < mu) :
    0 ≤ round4UnitNormalizationConstant N j mu Mraw hmu :=
  (Classical.choose_spec (actual_unit_normalization_slow_jets.{0} (N := N) j mu Mraw hmu)).1

/-- The actual two-projection and normalization cost depends on six numbers,
not on profiles of a current field or its compact coordinate domains. -/
def round4FreeProjectionConstant (N j : ℕ) (cA cB MA MB mu Mv : ℝ) (hmu : 0 < mu) : ℝ :=
  round4UnitNormalizationConstant N j mu
    (2^j * (2^j * actualFreeNormalProjectionCost j cB MB *
      actualFreeNormalProjectionCost j cA MA) * Mv) hmu

def round4OriginalNormalConstant (m N j : ℕ) (cF cT MA MH mu Mv : ℝ) (hmu : 0 < mu) : ℝ :=
  round4FreeProjectionConstant N j cF cT MA
    (actualIncrementTransverseFrameConstant m N j cF MA MH) mu Mv hmu

theorem round4OriginalNormalConstant_nonneg (m N j : ℕ)
    (cF cT MA MH mu Mv : ℝ) (hmu : 0 < mu) :
    0 ≤ round4OriginalNormalConstant m N j cF cT MA MH mu Mv hmu :=
  round4UnitNormalizationConstant_nonneg _ _ _ _ hmu

theorem round4_actual_unit_free_projection_field_slow_jets
    (j : ℕ) (cA cB MA MB mu Mv : ℝ)
    (hcA : 0 < cA) (hcB : 0 < cB) (hMA : 0 ≤ MA) (hMB : 0 ≤ MB)
    (hmu : 0 < mu) (hMv : 0 ≤ Mv) :
    let C := round4FreeProjectionConstant N j cA cB MA MB mu Mv hmu
    0 ≤ C ∧ ∀ {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
      (A : D → E →L[ℝ] V) (B : D → T →L[ℝ] V) (v : D → V) (O S : Set D)
      (_hO : IsOpen O) (_hSO : S ⊆ O)
      (_hA : ContDiffOn ℝ ∞ A O) (_hB : ContDiffOn ℝ ∞ B O) (_hv : ContDiffOn ℝ ∞ v O)
      (_hAi : ∀ x ∈ O, Function.Injective (A x))
      (_hBi : ∀ x ∈ O, Function.Injective (B x))
      (ell : ℝ) (_hell : 0 < ell),
      (∀ x ∈ S, ∀ w : E, cA*‖w‖^2 ≤ ‖A x w‖^2) →
      (∀ x ∈ S, ∀ w : T, cB*‖w‖^2 ≤ ‖B x w‖^2) →
      (∀ k ≤ j, ∀ x ∈ S, ell^k*‖iteratedFDeriv ℝ k A x‖ ≤ MA) →
      (∀ k ≤ j, ∀ x ∈ S, ell^k*‖iteratedFDeriv ℝ k B x‖ ≤ MB) →
      (∀ k ≤ j, ∀ x ∈ S, ell^k*‖iteratedFDeriv ℝ k v x‖ ≤ Mv) →
      (∀ x ∈ O, LinearMap.range (B x).toLinearMap ≤ (LinearMap.range (A x).toLinearMap)ᗮ) →
      (∀ x ∈ S, mu ≤ ‖actualFreeNormalProjectionRaw (A x) (B x) (v x)‖) →
      let raw := fun x => actualFreeNormalProjectionRaw (A x) (B x) (v x)
      ContDiffOn ℝ ∞ raw O ∧
      ContDiffOn ℝ ∞ (NormedSpace.normalize ∘ raw) (O ∩ raw ⁻¹' ({0}ᶜ : Set V)) ∧
      (∀ x ∈ S, ‖NormedSpace.normalize (raw x)‖ = 1 ∧
        NormedSpace.normalize (raw x) ∈ (LinearMap.range (A x).toLinearMap)ᗮ ∧
        NormedSpace.normalize (raw x) ∈ (LinearMap.range (B x).toLinearMap)ᗮ) ∧
      ∀ k ≤ j, ∀ x ∈ S, ell^k*‖iteratedFDeriv ℝ k (NormedSpace.normalize ∘ raw) x‖ ≤ C := by
  let PA := actualFreeNormalProjectionCost j cA MA
  let PB := actualFreeNormalProjectionCost j cB MB
  let Qb := 2^j*PB*PA
  let Mraw := 2^j*Qb*Mv
  have hPA : 0 ≤ PA := actualFreeNormalProjectionCost_nonneg j hcA hMA
  have hPB : 0 ≤ PB := actualFreeNormalProjectionCost_nonneg j hcB hMB
  have hQb : 0 ≤ Qb := by dsimp [Qb]; positivity
  obtain ⟨hC,hUnit⟩ := Classical.choose_spec
    (actual_unit_normalization_slow_jets.{0} (N := N) j mu Mraw hmu)
  refine ⟨hC,?_⟩
  intro D _ _ A B v O S hO hSO hA hB hv hAi hBi ell hell hAr hBr hAj hBj hvj hRange hReserve raw
  let QA := fun x => (LinearMap.range (A x).toLinearMap)ᗮ.starProjection
  let QB := fun x => (LinearMap.range (B x).toLinearMap)ᗮ.starProjection
  obtain ⟨hQA,hQAj⟩ := actual_normal_projection_slow_jets_on_samples A O S hO hSO hA hAi
    j ell cA MA hell hcA hMA hAr hAj
  obtain ⟨hQB,hQBj⟩ := actual_normal_projection_slow_jets_on_samples B O S hO hSO hB hBi
    j ell cB MB hell hcB hMB hBr hBj
  let Q : D → V →L[ℝ] V := fun x => (QB x).comp (QA x)
  have hQ : ContDiffOn ℝ ∞ Q O := hQB.clm_comp hQA
  have hQj : ∀ k ≤ j, ∀ x ∈ S, ell^k*‖iteratedFDeriv ℝ k Q x‖ ≤ Qb := by
    intro k hk x hx
    have hh := slow_bilinear_jet_bound (ContinuousLinearMap.compL ℝ V V V)
      (ContinuousLinearMap.norm_compL_le ℝ V V V) O hO QB QA hQB hQA k ell PB PA hell.le
      hPB x (hSO hx) (fun r hr => hQBj r (hr.trans hk) x hx)
      (fun r hr => hQAj r (hr.trans hk) x hx)
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) hPB) hPA)
  have hRaw : ContDiffOn ℝ ∞ raw O := hQ.clm_apply hv
  have hRawJets : ∀ k ≤ j, ∀ x ∈ S, ell^k*‖iteratedFDeriv ℝ k raw x‖ ≤ Mraw := by
    intro k hk x hx
    have hh := slow_bilinear_jet_bound (ContinuousLinearMap.id ℝ (V →L[ℝ] V))
      ContinuousLinearMap.norm_id_le O hO Q v hQ hv k ell Qb Mv hell.le hQb x (hSO hx)
      (fun r hr => hQj r (hr.trans hk) x hx) (fun r hr => hvj r (hr.trans hk) x hx)
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) hQb) hMv)
  obtain ⟨hNorm,hJets⟩ := hUnit O S hO hSO raw hRaw ell hell hReserve hRawJets
  refine ⟨hRaw,?_,?_,hJets⟩
  · exact actual_normalize_contDiffOn.comp (hRaw.mono inter_subset_left) (fun x hx => hx.2)
  · intro x hx
    have hm := actual_free_normal_projection_mem (A x) (B x) (v x) (hRange x (hSO hx))
    exact ⟨hNorm x hx,(LinearMap.range (A x).toLinearMap)ᗮ.smul_mem _ hm.1,
      (LinearMap.range (B x).toLinearMap)ᗮ.smul_mem _ hm.2⟩



end GlobalEmbedding.Continuation

open Manifold
set_option backward.isDefEq.respectTransparency false
namespace GlobalEmbedding.Continuation
variable {m N : ℕ} {Ep : Type} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
private local instance normalFirstNormed : NormedAddCommGroup (D →L[ℝ] V) := inferInstance
private local instance normalFirstSpace : NormedSpace ℝ (D →L[ℝ] V) := inferInstance
private local instance normalHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance normalHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance normalFrameNormed : NormedAddCommGroup (Tdata →L[ℝ] V) := inferInstance
private local instance normalFrameSpace : NormedSpace ℝ (Tdata →L[ℝ] V) := inferInstance
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

theorem round4_actual_original_unit_free_normal_field_slow_jets
    (j : ℕ) (cF cT MA MH mu Mv : ℝ)
    (hcF : 0 < cF) (hcT : 0 < cT) (hMA : 0 ≤ MA) (hMH : 0 ≤ MH)
    (hmu : 0 < mu) (hMv : 0 ≤ Mv) :
    let C := round4OriginalNormalConstant m N j cF cT MA MH mu Mv hmu
    0 ≤ C ∧ ∀
      (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
      (e : Ep → OpenPartialHomeomorph M D)
      (_he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
      (O S : Set X) (_hO : IsOpen O) (_hSO : S ⊆ O)
      (_hcoord : ∀ z ∈ O, z.2 ∈ (e z.1).target)
      (_hJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e z.1).symm z.2)) O)
      (_hImm : ∀ z ∈ O, Function.Injective (mfderiv 𝓙 𝓘(ℝ,V) (F z.1) ((e z.1).symm z.2)))
      (ell : ℝ) (_hell : 0 < ell),
      (∀ z ∈ S, ∀ w : D, cF*‖w‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2 w‖^2) →
      (∀ z ∈ O, ∀ w : Tdata, cT*‖w‖^2 ≤
        ‖incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (e z.1).symm z.2 w‖^2) →
      (∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k
        (fun y : X => fderiv ℝ (F y.1 ∘ (e y.1).symm) y.2) z‖ ≤ MA) →
      (∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k
        (fun y : X => fderiv ℝ (fderiv ℝ (F y.1 ∘ (e y.1).symm)) y.2) z‖ ≤ MH) →
      ∀ (v : X → V), ContDiffOn ℝ ∞ v O →
      (∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k v z‖ ≤ Mv) →
      (∀ z ∈ S, mu ≤ ‖actualOriginalFreeNormalFieldRaw F hF e v z‖) →
      ContDiffOn ℝ ∞ (actualOriginalUnitFreeNormalField F hF e v)
        (O ∩ (actualOriginalFreeNormalFieldRaw F hF e v) ⁻¹' ({0}ᶜ : Set V)) ∧
      (∀ z ∈ S, ∃ normal : normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2),
        (normal : V) = actualOriginalUnitFreeNormalField F hF e v z ∧ ‖normal‖ = 1 ∧
        incrementsTransversePairing (F z.1) (hF z.1) ((e z.1).symm z.2)
          (fun a : Fin m => incrementsModeCoordinateDirections (e z.1).symm z.2 a.succ) normal = 0) ∧
      ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k (actualOriginalUnitFreeNormalField F hF e v) z‖ ≤ C := by
  let MB := actualIncrementTransverseFrameConstant m N j cF MA MH
  have hMB : 0 ≤ MB := actualIncrementTransverseFrameConstant_nonneg m N j hcF hMA hMH
  obtain ⟨hC,hUnit⟩ := round4_actual_unit_free_projection_field_slow_jets (E := D) (T := Tdata) (N := N)
    j cF cT MA MB mu Mv hcF hcT hMA hMB hmu hMv
  refine ⟨hC,?_⟩
  intro F hF e he O S hO hSO hcoord hJoint hImm ell hell hFirst hFrame hAj hHj v hv hvJets hNormReserve
  let A := fun z : X => fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2
  let B := fun z : X => incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (e z.1).symm z.2
  obtain ⟨hSlice,hA,hH⟩ := incrementsJointSpatialJets_bridge _ O hO hJoint
  have hAInj (z : X) (hz : z ∈ O) : Function.Injective (A z) :=
    actual_increment_chart_derivative_injective (F z.1) (hF z.1) (e z.1) (he z.1) z.2
      (hcoord z hz) (hImm z hz)
  obtain ⟨hQ,hQj⟩ := actual_increment_projected_hessian_slow_jets_on_samples F hF e he O S hO hSO
    hcoord hA hH hAInj j ell cF MA MH hell hcF hMA hMH hFirst hAj hHj
  obtain ⟨hRows,hB⟩ := actual_true_geometry_from_normal_hessian_on_samples F hF e he O S hO hSO
    hcoord hQ j ell (actualIncrementSecondFormConstant m N j cF MA MH) hell.le hQj
  have hBInj (z : X) (hz : z ∈ O) : Function.Injective (B z) :=
    actual_frame_injective_of_reserve _ cT hcT (hFrame z hz)
  have hRange (z : X) (hz : z ∈ O) :
      LinearMap.range (B z).toLinearMap ≤ (LinearMap.range (A z).toLinearMap)ᗮ := by
    rintro w ⟨t,rfl⟩
    rw [← actual_increment_normalSpace_eq_chart_range (F z.1) (hF z.1)
      (e z.1) (he z.1) z.2 (hcoord z hz)]
    change incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (e z.1).symm z.2 t ∈ _
    rw [incrementsModeAmbientTransverseFrame_eq]
    exact ((incrementsTransversePairing (F z.1) (hF z.1) ((e z.1).symm z.2)
      (fun a : Fin m => incrementsModeCoordinateDirections (e z.1).symm z.2 a.succ)).adjoint t).property
  obtain ⟨hRaw,hSmooth,hLegal,hJets⟩ := hUnit A B v O S hO hSO hA hB.1 hv hAInj hBInj ell hell
    hFirst (fun z hz => hFrame z (hSO hz)) hAj hB.2 hvJets hRange hNormReserve
  refine ⟨hSmooth,?_,hJets⟩
  intro z hz
  obtain ⟨hNorm,hNormal,hTransverse⟩ := hLegal z hz
  have hm : actualOriginalUnitFreeNormalField F hF e v z ∈
      normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2) := by
    rw [actual_increment_normalSpace_eq_chart_range (F z.1) (hF z.1) (e z.1) (he z.1)
      z.2 (hcoord z (hSO hz))]
    exact hNormal
  let normal : normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2) := ⟨_,hm⟩
  exact ⟨normal,rfl,hNorm,actual_original_normal_beta_of_frame_orthogonal
    (F z.1) (hF z.1) (e z.1).symm z.2 normal hTransverse⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_actual_original_unit_free_normal_field_slow_jets
#print axioms GlobalEmbedding.Continuation.round4_actual_unit_free_projection_field_slow_jets
