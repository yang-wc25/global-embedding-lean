import Probes.ActualFreeNormalFieldSlowJets
import Probes.ActualOriginalUnitFreeNormalLegal
import Probes.ActualIncrementSampleNormalTransfer
import Probes.ActualIncrementCompactOpenReserves

/-! A literal unit free normal for the SAME actual map and selected phase chart.
The first frame is its native spatial derivative and the transverse frame is
its actual true second form. Frame jets are produced from the map's first and
Hessian jets. No unit field or normal derivative bound is supplied.
The reference field can vary jointly; its own original jets are consumed.
The new unit field and all its derivative budgets are internally constructed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
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

def actualOriginalFreeNormalFieldRaw
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (e : Ep → OpenPartialHomeomorph M D) (v : X → V) (z : X) : V :=
  actualFreeNormalProjectionRaw
    (fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2)
    (incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (e z.1).symm z.2) (v z)

def actualOriginalUnitFreeNormalField
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (e : Ep → OpenPartialHomeomorph M D) (v : X → V) : X → V :=
  NormedSpace.normalize ∘ actualOriginalFreeNormalFieldRaw F hF e v

theorem actual_original_unit_free_normal_field_slow_jets
    (j : ℕ) (cF cT MA MH mu Mv : ℝ)
    (hcF : 0 < cF) (hcT : 0 < cT) (hMA : 0 ≤ MA) (hMH : 0 ≤ MH)
    (hmu : 0 < mu) (hMv : 0 ≤ Mv) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀
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
  obtain ⟨C,hC,hUnit⟩ := actual_unit_free_projection_field_slow_jets (E := D) (T := Tdata) (N := N)
    j cF cT MA MB mu Mv hcF hcT hMA hMB hmu hMv
  refine ⟨C,hC,?_⟩
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
#print axioms GlobalEmbedding.Continuation.actual_original_unit_free_normal_field_slow_jets
