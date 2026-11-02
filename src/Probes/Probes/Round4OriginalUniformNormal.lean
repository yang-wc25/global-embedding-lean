import Probes.Round4OriginalNormalDimension
import Probes.Round4UniformFreeNormalNeighborhood
import Probes.ActualOriginalFreeNormalField

/-!
The original N >= s_n + 1 dimension condition and the actual map jets
produce a uniform local unit free normal. Its ambient coordinate is selected
internally. Neither an initial normal nor a lower bound on its double
projection is an input. The neighborhood radius uses only map jets through
spatial order three and the first/transverse coercivity margins.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Function Metric
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
private local instance uniformOriginalFirstNormed : NormedAddCommGroup (D →L[ℝ] V) := inferInstance
private local instance uniformOriginalFirstSpace : NormedSpace ℝ (D →L[ℝ] V) := inferInstance
private local instance uniformOriginalHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance uniformOriginalHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance uniformOriginalFrameNormed : NormedAddCommGroup (Tdata →L[ℝ] V) := inferInstance
private local instance uniformOriginalFrameSpace : NormedSpace ℝ (Tdata →L[ℝ] V) := inferInstance
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

def round4OriginalNormalRadius (m N : ℕ) (cF cT MA MH : ℝ) : ℝ :=
  round4FreeNormalNeighborhoodRadius N cF cT MA
    (actualIncrementTransverseFrameConstant m N 1 cF MA MH)

theorem round4_actual_original_uniform_normal
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (e : Ep → OpenPartialHomeomorph M D)
    (he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set X) (hO : IsOpen O) (hConv : Convex ℝ O)
    (hcoord : ∀ z ∈ O, z.2 ∈ (e z.1).target)
    (hJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e z.1).symm z.2)) O)
    (cF cT MA MH : ℝ) (hcF : 0 < cF) (hcT : 0 < cT)
    (hMA : 0 ≤ MA) (hMH : 0 ≤ MH)
    (hFirst : ∀ z ∈ O, ∀ w : D,
      cF*‖w‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2 w‖^2)
    (hFrame : ∀ z ∈ O, ∀ w : Tdata, cT*‖w‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (e z.1).symm z.2 w‖^2)
    (hAj : ∀ k ≤ 1, ∀ z ∈ O, ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (F y.1 ∘ (e y.1).symm) y.2) z‖ ≤ MA)
    (hHj : ∀ k ≤ 1, ∀ z ∈ O, ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (fderiv ℝ (F y.1 ∘ (e y.1).symm)) y.2) z‖ ≤ MH)
    (hdim : (m+1)*(m+2)/2 < N) (x : X) (hx : x ∈ O) :
    let rho := round4OriginalNormalRadius m N cF cT MA MH
    0 < rho ∧ ∃ i : Fin N,
      ContDiffOn ℝ ∞ (actualOriginalUnitFreeNormal F hF e (EuclideanSpace.single i 1))
        (O ∩ ball x rho) ∧
      ∀ z ∈ O ∩ ball x rho,
        round4AmbientCoordinateReserve N / 2 ≤
          ‖actualOriginalFreeNormalRaw F hF e (EuclideanSpace.single i 1) z‖ ∧
        ∃ normal : normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2),
          (normal : V) = actualOriginalUnitFreeNormal F hF e (EuclideanSpace.single i 1) z ∧
          ‖normal‖ = 1 ∧
          incrementsTransversePairing (F z.1) (hF z.1) ((e z.1).symm z.2)
            (fun a : Fin m => incrementsModeCoordinateDirections (e z.1).symm z.2 a.succ) normal = 0 := by
  let A := fun z : X => fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2
  let B := fun z : X => incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (e z.1).symm z.2
  let MB := actualIncrementTransverseFrameConstant m N 1 cF MA MH
  have hMB : 0 ≤ MB := actualIncrementTransverseFrameConstant_nonneg m N 1 hcF hMA hMH
  obtain ⟨hSlice, hA, hH⟩ := incrementsJointSpatialJets_bridge _ O hO hJoint
  obtain ⟨hB, hBj⟩ := actual_increment_transverse_frame_slow_jets F hF e he O hO hcoord
    hA hH 1 1 cF MA MH (by norm_num) hcF hMA hMH hFirst
    (by simpa only [one_pow, one_mul] using hAj)
    (by simpa only [one_pow, one_mul] using hHj)
  have hRange (z : X) (hz : z ∈ O) :
      LinearMap.range (B z).toLinearMap ≤ (LinearMap.range (A z).toLinearMap)ᗮ := by
    rintro w ⟨t,rfl⟩
    rw [← actual_increment_normalSpace_eq_chart_range (F z.1) (hF z.1)
      (e z.1) (he z.1) z.2 (hcoord z hz)]
    change incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (e z.1).symm z.2 t ∈ _
    rw [incrementsModeAmbientTransverseFrame_eq]
    exact ((incrementsTransversePairing (F z.1) (hF z.1) ((e z.1).symm z.2)
      (fun a : Fin m => incrementsModeCoordinateDirections (e z.1).symm z.2 a.succ)).adjoint t).property
  obtain ⟨hrho, i, hSmooth, hLegal⟩ := round4_actual_uniform_free_normal_neighborhood
    cF cT MA MB hcF hcT hMA hMB A B O hO hConv hA hB hFirst hFrame hAj
    (by simpa only [one_pow, one_mul] using hBj)
    (round4_original_normal_rank_deficit m N hdim) hRange x hx
  refine ⟨hrho, i, hSmooth, ?_⟩
  intro z hz
  obtain ⟨hRes, hNorm, hNormal, hTransverse⟩ := hLegal z hz
  refine ⟨hRes, ?_⟩
  have hm : actualOriginalUnitFreeNormal F hF e (EuclideanSpace.single i 1) z ∈
      normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2) := by
    rw [actual_increment_normalSpace_eq_chart_range (F z.1) (hF z.1) (e z.1) (he z.1)
      z.2 (hcoord z hz.1)]
    exact hNormal
  let normal : normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2) := ⟨_,hm⟩
  exact ⟨normal, rfl, hNorm, actual_original_normal_beta_of_frame_orthogonal
    (F z.1) (hF z.1) (e z.1).symm z.2 normal hTransverse⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_actual_original_uniform_normal
