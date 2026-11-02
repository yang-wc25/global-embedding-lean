import Probes.ActualFreeNormalProjection
import Probes.ActualIncrementSampleNormalTransfer
import Probes.ActualIncrementCompactOpenReserves

/-! A literal unit free normal for the SAME actual map and selected phase chart.
The first frame is its native spatial derivative and the transverse frame is
its actual true second form. Frame jets are produced from the map's first and
Hessian jets. No unit field or normal derivative bound is supplied.
The scalar projection margin concerns only the actual fixed ambient vector. -/

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

def actualOriginalFreeNormalRaw
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (e : Ep → OpenPartialHomeomorph M D) (v : V) (z : X) : V :=
  actualFreeNormalProjectionRaw
    (fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2)
    (incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (e z.1).symm z.2) v

def actualOriginalUnitFreeNormal
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (e : Ep → OpenPartialHomeomorph M D) (v : V) : X → V :=
  NormedSpace.normalize ∘ actualOriginalFreeNormalRaw F hF e v

theorem actual_original_normal_beta_of_frame_orthogonal
    (F : M → V) (hF : ContMDiff 𝓙 𝓘(ℝ,V) ∞ F) (c : D → M) (x : D)
    (v : normalSpace (I := 𝓙) F (c x))
    (hv : (v : V) ∈ (LinearMap.range
      (incrementsModeAmbientTransverseFrame F hF c x).toLinearMap)ᗮ) :
    incrementsTransversePairing F hF (c x)
      (fun a : Fin m => incrementsModeCoordinateDirections c x a.succ) v = 0 := by
  let beta := incrementsTransversePairing F hF (c x)
    (fun a : Fin m => incrementsModeCoordinateDirections c x a.succ)
  apply ext_inner_left ℝ
  intro t
  rw [inner_zero_right,← beta.adjoint_inner_left v t]
  change inner ℝ ((beta.adjoint t : normalSpace (I := 𝓙) F (c x)) : V) (v : V) = 0
  have hh := (Submodule.mem_orthogonal _ _).mp hv
    (incrementsModeAmbientTransverseFrame F hF c x t) ⟨t,rfl⟩
  have he := congrArg (fun L : Tdata →L[ℝ] V => L t)
    (incrementsModeAmbientTransverseFrame_eq F hF c x)
  change incrementsModeAmbientTransverseFrame F hF c x t = (beta.adjoint t : V) at he
  rwa [he] at hh

theorem actual_original_unit_free_normal_slow_jets
    (j : ℕ) (cF cT MA MH mu Bv : ℝ)
    (hcF : 0 < cF) (hcT : 0 < cT) (hMA : 0 ≤ MA) (hMH : 0 ≤ MH)
    (hmu : 0 < mu) (hBv : 0 ≤ Bv) :
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
      ∀ (v : V), ‖v‖ ≤ Bv → (∀ z ∈ S, mu ≤ ‖actualOriginalFreeNormalRaw F hF e v z‖) →
      ContDiffOn ℝ ∞ (actualOriginalUnitFreeNormal F hF e v)
        (O ∩ (actualOriginalFreeNormalRaw F hF e v) ⁻¹' ({0}ᶜ : Set V)) ∧
      (∀ z ∈ S, ∃ normal : normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2),
        (normal : V) = actualOriginalUnitFreeNormal F hF e v z ∧ ‖normal‖ = 1 ∧
        incrementsTransversePairing (F z.1) (hF z.1) ((e z.1).symm z.2)
          (fun a : Fin m => incrementsModeCoordinateDirections (e z.1).symm z.2 a.succ) normal = 0) ∧
      ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k (actualOriginalUnitFreeNormal F hF e v) z‖ ≤ C := by
  let MB := actualIncrementTransverseFrameConstant m N j cF MA MH
  have hMB : 0 ≤ MB := actualIncrementTransverseFrameConstant_nonneg m N j hcF hMA hMH
  obtain ⟨C,hC,hUnit⟩ := actual_unit_free_projection_slow_jets (E := D) (T := Tdata) (N := N)
    j cF cT MA MB mu Bv hcF hcT hMA hMB hmu hBv
  refine ⟨C,hC,?_⟩
  intro F hF e he O S hO hSO hcoord hJoint hImm ell hell hFirst hFrame hAj hHj v hv hNormReserve
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
  obtain ⟨hRaw,hSmooth,hLegal,hJets⟩ := hUnit A B O S hO hSO hA hB.1 hAInj hBInj ell hell
    hFirst (fun z hz => hFrame z (hSO hz)) hAj hB.2 hRange v hv hNormReserve
  refine ⟨hSmooth,?_,hJets⟩
  intro z hz
  obtain ⟨hNorm,hNormal,hTransverse⟩ := hLegal z hz
  have hm : actualOriginalUnitFreeNormal F hF e v z ∈
      normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2) := by
    rw [actual_increment_normalSpace_eq_chart_range (F z.1) (hF z.1) (e z.1) (he z.1)
      z.2 (hcoord z (hSO hz))]
    exact hNormal
  let normal : normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2) := ⟨_,hm⟩
  exact ⟨normal,rfl,hNorm,actual_original_normal_beta_of_frame_orthogonal
    (F z.1) (hF z.1) (e z.1).symm z.2 normal hTransverse⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_normal_beta_of_frame_orthogonal
#print axioms GlobalEmbedding.Continuation.actual_original_unit_free_normal_slow_jets
