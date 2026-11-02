import Upgrade.CompactProbeAtlas
import Upgrade.SupportedProbeAtlasTransport
import GlobalEmbedding.Offline.ActualHessianJet

/-!
# The original atlas C² norm controls the actual fixed coordinate jets

These are derivatives of the literal maps composed with the original chart
inverse.  The source norm is the fixed Euclidean model; no varying `chartAt x`
norm or Riemannian metric is introduced.  The support set is only a norm domain,
and need not have interior.  Its containing differentiation domain stays open.
-/

noncomputable section
open Set Bundle Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.Upgrade

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

section CoordinateComparison
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n N : ℕ}

/-- The existing original component-norm bound can be used at every point of
its specified norm domain, including its boundary. Only the outer domain is
used for differentiation. The source/target conversion factors are literal
operator norms and the accepted derivative-order factor. -/
theorem iteratedFDeriv_le_of_euclidean_coordinate_bound_at_normDomain
    (e : E ≃L[ℝ] (Fin n → ℝ)) (u : E → EuclideanSpace ℝ (Fin N))
    {O S : Set (Fin n → ℝ)} (hO : IsOpen O) (hSO : S ⊆ O)
    (hu : ContDiffOn ℝ ∞ (euclideanCoordinateRepresentative e u) O)
    {j a : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (hbound : paperCoordinateCj j (euclideanCoordinateRepresentative e u) O S ≤
      ENNReal.ofReal b) (ha : a ≤ j) {x : E} (hx : e x ∈ S) :
    ‖iteratedFDeriv ℝ a u x‖ ≤
      ‖(EuclideanSpace.equiv (Fin N) ℝ).symm.toContinuousLinearMap‖ *
        ((n : ℝ) ^ a * b) * ‖e.toContinuousLinearMap‖ ^ a := by
  let c := euclideanCoordinateRepresentative e u
  let L := (EuclideanSpace.equiv (Fin N) ℝ).symm
  have heq : u = L ∘ (c ∘ e) := by
    funext y
    simp only [L, c, euclideanCoordinateRepresentative, Function.comp_apply,
      ContinuousLinearEquiv.symm_apply_apply]
  have hV : IsOpen (e ⁻¹' O) := hO.preimage e.continuous
  have hxO : e x ∈ O := hSO hx
  have hc : ‖iteratedFDerivWithin ℝ a c O (e x)‖ ≤ (n : ℝ) ^ a * b := by
    rw [iteratedFDerivWithin_of_isOpen a hO hxO]
    exact iteratedFDeriv_le_of_paperCoordinateCj_le hO hSO hu hb hbound ha hx
  rw [← iteratedFDerivWithin_of_isOpen a hV hxO, heq,
    L.iteratedFDerivWithin_comp_left _ hV.uniqueDiffOn hxO a,
    e.iteratedFDerivWithin_comp_right c hO.uniqueDiffOn hxO a]
  have hsource := (iteratedFDerivWithin ℝ a c O (e x)).norm_compContinuousLinearMap_le
    (fun _ : Fin a ↦ e.toContinuousLinearMap)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hsource
  calc
    _ ≤ ‖L.toContinuousLinearMap‖ *
        ‖(iteratedFDerivWithin ℝ a c O (e x)).compContinuousLinearMap
          (fun _ : Fin a ↦ e.toContinuousLinearMap)‖ :=
      L.toContinuousLinearMap.norm_compContinuousMultilinearMap_le _
    _ ≤ ‖L.toContinuousLinearMap‖ *
        (‖iteratedFDerivWithin ℝ a c O (e x)‖ * ‖e.toContinuousLinearMap‖ ^ a) :=
      mul_le_mul_of_nonneg_left hsource (norm_nonneg _)
    _ ≤ ‖L.toContinuousLinearMap‖ *
        (((n : ℝ) ^ a * b) * ‖e.toContinuousLinearMap‖ ^ a) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hc (pow_nonneg (norm_nonneg _) _)) (norm_nonneg _)
    _ = _ := by dsimp only [L]; ring

end CoordinateComparison

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

def probeAtlasDerivativeConstant (n N a : ℕ) : ℝ :=
  ‖(EuclideanSpace.equiv (Fin N) ℝ).symm.toContinuousLinearMap‖ *
    (n : ℝ) ^ a * ‖(EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap‖ ^ a

theorem probeAtlasDerivativeConstant_nonneg (n N a : ℕ) :
    0 ≤ probeAtlasDerivativeConstant n N a := by
  unfold probeAtlasDerivativeConstant
  positivity

/-- Actual fixed-coordinate differential. -/
def probeAtlasFirstJet (A : BufferedAtlas M E) (F : M → V)
    (i : Fin A.count) (x : M) : E →L[ℝ] V :=
  fderiv ℝ (F ∘ (A.chart i).symm) (A.chart i x)

/-- Actual fixed-coordinate Hessian descended to the original Sym² quotient. -/
def probeAtlasSecondJet (A : BufferedAtlas M E) (F : M → V)
    (i : Fin A.count) (x : M) : SymmetricSquare E →L[ℝ] V :=
  coordinateHessianJet (F ∘ (A.chart i).symm) (A.chart i x)

theorem probeAtlas_fixed_coordinate_smooth
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F) (i : Fin A.count) :
    ContDiffOn ℝ ∞ (F ∘ (A.chart i).symm) (A.chart i).target :=
  (hF.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem i))).contDiffOn

/-- The actual original atlas bound supplies the fixed-coordinate native
derivative estimates at every actual enlarged-support point. -/
theorem probeAtlas_native_derivative_bound
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    {j a : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (hbound : probeAtlasCj A j F ≤ ENNReal.ofReal b) (ha : a ≤ j)
    (i : Fin A.count) (x : M) (hx : x ∈ A.support i) :
    ‖iteratedFDeriv ℝ a (F ∘ (A.chart i).symm) (A.chart i x)‖ ≤
      probeAtlasDerivativeConstant n N a * b := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  let O := e '' (A.chart i).target
  let S := e '' ((A.chart i) '' A.support i)
  have hO : IsOpen O := e.toHomeomorph.isOpenMap _ (A.chart i).open_target
  have hSO : S ⊆ O := by
    rintro y ⟨z, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨A.chart i p, (A.chart i).map_source (hA.support_subset i hp), rfl⟩
  have hsmooth : ContDiffOn ℝ ∞
      (euclideanCoordinateRepresentative e (F ∘ (A.chart i).symm)) O :=
    probeAtlas_coordinate_smooth A hA F hF i
  have hlocal : paperCoordinateCj j
      (euclideanCoordinateRepresentative e (F ∘ (A.chart i).symm)) O S ≤
        ENNReal.ofReal b := (le_iSup
          (fun k ↦ paperCoordinateCj j
            (fun y ↦ (EuclideanSpace.equiv (Fin N) ℝ)
              (F ((A.chart k).symm (e.symm y))))
            (e '' (A.chart k).target) (e '' ((A.chart k) '' A.support k))) i).trans hbound
  have h := iteratedFDeriv_le_of_euclidean_coordinate_bound_at_normDomain e
    (F ∘ (A.chart i).symm) hO hSO hsmooth hb hlocal ha
    (show e (A.chart i x) ∈ S from ⟨A.chart i x, ⟨x, hx, rfl⟩, rfl⟩)
  convert h using 1
  unfold probeAtlasDerivativeConstant
  dsimp only [e]
  ring

/-- Original C² displacement controls the literal first and second fixed
coordinate jets of two actual smooth maps. No independently supplied Hessian
or assumed second-form estimate occurs here. -/
theorem probeAtlas_original_two_jet_difference
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F G : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F) (hG : ContMDiff IM 𝓘(ℝ, V) ∞ G)
    {b : ℝ} (hb : 0 ≤ b) (hbound : probeAtlasCj A 2 (G - F) ≤ ENNReal.ofReal b)
    (i : Fin A.count) (x : M) (hx : x ∈ A.support i) :
    ‖probeAtlasFirstJet A G i x - probeAtlasFirstJet A F i x‖ ≤
      probeAtlasDerivativeConstant n N 1 * b ∧
    ‖probeAtlasSecondJet A G i x - probeAtlasSecondJet A F i x‖ ≤
      (actualHessianLiftConstant E V * probeAtlasDerivativeConstant n N 2) * b := by
  have hxT := (A.chart i).map_source (hA.support_subset i hx)
  have hFc : ContDiffAt ℝ 2 (F ∘ (A.chart i).symm) (A.chart i x) :=
    ((probeAtlas_fixed_coordinate_smooth A hA F hF i).contDiffAt
      ((A.chart i).open_target.mem_nhds hxT)).of_le (by simp)
  have hGc : ContDiffAt ℝ 2 (G ∘ (A.chart i).symm) (A.chart i x) :=
    ((probeAtlas_fixed_coordinate_smooth A hA G hG i).contDiffAt
      ((A.chart i).open_target.mem_nhds hxT)).of_le (by simp)
  have hjet (a : ℕ) (ha : a ≤ 2) := probeAtlas_native_derivative_bound
    A hA (G - F) (hG.sub hF) hb hbound ha i x hx
  constructor
  · have heq : probeAtlasFirstJet A G i x - probeAtlasFirstJet A F i x =
        fderiv ℝ ((G - F) ∘ (A.chart i).symm) (A.chart i x) := by
      exact (fderiv_sub (hGc.differentiableAt (by simp))
        (hFc.differentiableAt (by simp))).symm
    rw [heq, ← norm_iteratedFDeriv_one]
    exact hjet 1 (by norm_num)
  · have hsecond := coordinateHessianJet_sub_norm_le hGc hFc
    have hbound2 := mul_le_mul_of_nonneg_left (hjet 2 le_rfl)
      (show 0 ≤ actualHessianLiftConstant E V from actualHessianLiftConstant_nonneg)
    have h := hsecond.trans hbound2
    simpa only [probeAtlasSecondJet, Function.comp_def, Pi.sub_apply, mul_assoc] using h

end GlobalEmbedding.Upgrade
