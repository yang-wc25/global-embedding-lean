import NormalPolar.FullResponse

/-!
# Actual parameter-response tails in the original atlas C² norm

These results consume the genuine parameter derivative of a correction to
the actual mapping family. They commute its two spatial derivatives from
joint smoothness, then apply the original coordinate C² budget. No estimate
of an identified second form, a normal identification or a prescribed tail
is assumed. The actual construction and estimates of repair tails remain
upstream.
-/

noncomputable section
open Set Filter Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade

section MixedSecond
variable {P X Y : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The parameter derivative of the genuine spatial Hessian is the spatial
Hessian of the genuine parameter response, on the same open domain. -/
theorem actual_parameter_spatial_second_fderiv_comm
    {Ω : Set (P × X)} (hΩ : IsOpen Ω) (f : P × X → Y)
    (hf : ContDiffOn ℝ ∞ f Ω) (u : P) (x : X) (d : P)
    (hux : (u, x) ∈ Ω) :
    fderiv ℝ (fun v ↦ fderiv ℝ (fderiv ℝ (fun s ↦ f (v, s))) x) u d =
      fderiv ℝ (fderiv ℝ (fun s ↦ fderiv ℝ (fun v ↦ f (v, s)) u d)) x := by
  have hD := contDiffOn_actual_spatial_fderiv hΩ hf
  have hsecond := actual_parameter_spatial_fderiv_comm
    (fun z : P × X ↦ fderiv ℝ (fun s ↦ f (z.1, s)) z.2) u x d
    (hD.contDiffAt (hΩ.mem_nhds hux))
  have hnear : ∀ᶠ s in 𝓝 x, (u, s) ∈ Ω :=
    (continuous_const.prodMk continuous_id).continuousAt.eventually (hΩ.mem_nhds hux)
  have heq : (fun s ↦ fderiv ℝ (fun v ↦ fderiv ℝ (fun q ↦ f (v, q)) s) u d)
      =ᶠ[𝓝 x] (fun s ↦ fderiv ℝ (fun q ↦ fderiv ℝ (fun v ↦ f (v, q)) u d) s) := by
    filter_upwards [hnear] with s hs
    exact actual_parameter_spatial_fderiv_comm f u s d
      (hf.contDiffAt (hΩ.mem_nhds hs))
  exact hsecond.trans heq.fderiv_eq

/-- Subtraction is compatible with the actual second derivative on an open
smoothness domain, including the neighborhood needed for the inner derivative. -/
theorem actual_spatial_second_fderiv_sub
    {O : Set X} (hO : IsOpen O) (f g : X → Y)
    (hf : ContDiffOn ℝ ∞ f O) (hg : ContDiffOn ℝ ∞ g O)
    (x : X) (hx : x ∈ O) :
    fderiv ℝ (fderiv ℝ (fun s ↦ f s - g s)) x =
      fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ g) x := by
  have heq : (fderiv ℝ (fun s ↦ f s - g s)) =ᶠ[𝓝 x]
      (fun s ↦ fderiv ℝ f s - fderiv ℝ g s) := by
    filter_upwards [hO.mem_nhds hx] with s hs
    exact fderiv_sub ((hf.contDiffAt (hO.mem_nhds hs)).differentiableAt (by simp))
      ((hg.contDiffAt (hO.mem_nhds hs)).differentiableAt (by simp))
  rw [heq.fderiv_eq]
  have hfD : ContDiffAt ℝ ∞ (fderiv ℝ f) x :=
    (hf.contDiffAt (hO.mem_nhds hx)).fderiv_right (by simp)
  have hgD : ContDiffAt ℝ ∞ (fderiv ℝ g) x :=
    (hg.contDiffAt (hO.mem_nhds hx)).fderiv_right (by simp)
  exact fderiv_sub
    (hfD.differentiableAt (by simp)) (hgD.differentiableAt (by simp))

end MixedSecond

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ, E)

private noncomputable local instance tailBilinearSemi :
    SeminormedAddCommGroup (E →L[ℝ] E →L[ℝ] V) := ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance tailBilinearNorm :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] V) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance tailBilinearSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] V) := ContinuousLinearMap.toNormedSpace

/-- Original atlas Cʲ control bounds native derivatives if smoothness of the
actual coordinate representative has already been obtained from a joint family.
This avoids requiring an unrelated global derivative-field smoothness input. -/
theorem probeAtlas_native_derivative_bound_of_chart_smooth
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F : M → V) (i : Fin A.count)
    (hF : ContDiffOn ℝ ∞ (F ∘ (A.chart i).symm) (A.chart i).target)
    {j a : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (hbound : probeAtlasCj A j F ≤ ENNReal.ofReal b) (ha : a ≤ j)
    (x : M) (hx : x ∈ A.support i) :
    ‖iteratedFDeriv ℝ a (F ∘ (A.chart i).symm) (A.chart i x)‖ ≤
      probeAtlasDerivativeConstant n N a * b := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  let O := e '' (A.chart i).target
  let S := e '' ((A.chart i) '' A.support i)
  have hO : IsOpen O := e.toHomeomorph.isOpenMap _ (A.chart i).open_target
  have hSO : S ⊆ O := by
    rintro y ⟨s, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨A.chart i p, (A.chart i).map_source (hA.support_subset i hp), rfl⟩
  have hsmooth : ContDiffOn ℝ ∞
      (euclideanCoordinateRepresentative e (F ∘ (A.chart i).symm)) O := by
    apply (EuclideanSpace.equiv (Fin N) ℝ).contDiff.comp_contDiffOn
    apply hF.comp e.symm.contDiff.contDiffOn
    rintro y ⟨s, hs, rfl⟩
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hs
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

section ActualFamily
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Coordinates of the actual parameter response are smooth, derived directly
from the supplied actual family on its original open parameter domain. -/
theorem atlas_actual_parameter_response_contDiffOn
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    {U : Set P} (hU : IsOpen U) (F : P → M → V)
    (hF : ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V) ∞
      (Function.uncurry F) (U ×ˢ univ))
    (u d : P) (hu : u ∈ U) :
    ContDiffOn ℝ ∞
      ((fun y ↦ fderiv ℝ (fun v ↦ F v y) u d) ∘ (A.chart i).symm)
      (A.chart i).target := by
  have hf := contDiffOn_actual_parameter_atlas_pullback A hA i (Function.uncurry F) hF
  have hD := (contDiffOn_actual_parameter_fderiv
    (hU.prod (A.chart i).open_target) hf).clm_apply (contDiffOn_const (c := d))
  apply hD.comp (contDiff_const.prodMk contDiff_id).contDiffOn
  intro s hs
  exact ⟨hu, hs⟩

/-- Exact native mixed-derivative identity in the given actual atlas. -/
theorem atlas_native_hessian_response_eq
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    {U : Set P} (hU : IsOpen U) (F : P → M → V)
    (hF : ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V) ∞
      (Function.uncurry F) (U ×ˢ univ))
    (u d : P) (hu : u ∈ U) (x : M) (hx : x ∈ (A.chart i).source) :
    fderiv ℝ (fun v ↦ fderiv ℝ (fderiv ℝ (F v ∘ (A.chart i).symm)) (A.chart i x)) u d =
      fderiv ℝ (fderiv ℝ
        ((fun y ↦ fderiv ℝ (fun v ↦ F v y) u d) ∘ (A.chart i).symm)) (A.chart i x) := by
  exact actual_parameter_spatial_second_fderiv_comm
    (hU.prod (A.chart i).open_target)
    (fun z : P × E ↦ F z.1 ((A.chart i).symm z.2))
    (contDiffOn_actual_parameter_atlas_pullback A hA i (Function.uncurry F) hF)
    u (A.chart i x) d ⟨hu, (A.chart i).map_source hx⟩

/-- A genuine original C² bound for the actual parameter-response difference
controls the difference of the two actual native Hessian responses. Both
families use the same parameter domain and the same atlas coordinate. -/
theorem atlas_native_hessian_response_difference_bound_of_originalC2
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    {U : Set P} (hU : IsOpen U) (F G : P → M → V)
    (hF : ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V) ∞
      (Function.uncurry F) (U ×ˢ univ))
    (hG : ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V) ∞
      (Function.uncurry G) (U ×ˢ univ))
    (u d : P) (hu : u ∈ U) (x : M) (hx : x ∈ A.support i)
    {b : ℝ} (hb : 0 ≤ b)
    (htail : probeAtlasCj A 2
      (fun y ↦ fderiv ℝ (fun v ↦ F v y) u d -
        fderiv ℝ (fun v ↦ G v y) u d) ≤ ENNReal.ofReal b) :
    ‖fderiv ℝ (fun v ↦ fderiv ℝ (fderiv ℝ (F v ∘ (A.chart i).symm)) (A.chart i x)) u d -
      fderiv ℝ (fun v ↦ fderiv ℝ (fderiv ℝ (G v ∘ (A.chart i).symm)) (A.chart i x)) u d‖ ≤
        probeAtlasDerivativeConstant n N 2 * b := by
  let RF := fun y ↦ fderiv ℝ (fun v ↦ F v y) u d
  let RG := fun y ↦ fderiv ℝ (fun v ↦ G v y) u d
  have hRF := atlas_actual_parameter_response_contDiffOn A hA i hU F hF u d hu
  have hRG := atlas_actual_parameter_response_contDiffOn A hA i hU G hG u d hu
  have hR : ContDiffOn ℝ ∞ ((fun y ↦ RF y - RG y) ∘ (A.chart i).symm)
      (A.chart i).target := hRF.sub hRG
  have hbound := probeAtlas_native_derivative_bound_of_chart_smooth A hA
    (fun y ↦ RF y - RG y) i hR hb htail (show 2 ≤ 2 by rfl) x hx
  rw [atlas_native_hessian_response_eq A hA i hU F hF u d hu x (hA.support_subset i hx),
    atlas_native_hessian_response_eq A hA i hU G hG u d hu x (hA.support_subset i hx)]
  have hsub := actual_spatial_second_fderiv_sub (A.chart i).open_target
    (RF ∘ (A.chart i).symm) (RG ∘ (A.chart i).symm) hRF hRG (A.chart i x)
    ((A.chart i).map_source (hA.support_subset i hx))
  rw [← hsub]
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  exact hbound

/-- Transfer a proved native Hessian response from an actual preliminary
family to the final actual family using its original C² parameter tail.
The principal tensor is unchanged. -/
theorem atlas_native_hessian_response_bound_of_originalC2_tail
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    {U : Set P} (hU : IsOpen U) (F G : P → M → V)
    (hF : ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V) ∞
      (Function.uncurry F) (U ×ˢ univ))
    (hG : ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V) ∞
      (Function.uncurry G) (U ×ˢ univ))
    (u d : P) (hu : u ∈ U) (x : M) (hx : x ∈ A.support i)
    (H : E →L[ℝ] E →L[ℝ] V) {e b : ℝ} (hb : 0 ≤ b)
    (hmodel : ‖fderiv ℝ
      (fun v ↦ fderiv ℝ (fderiv ℝ (G v ∘ (A.chart i).symm)) (A.chart i x)) u d - H‖ ≤ e)
    (htail : probeAtlasCj A 2
      (fun y ↦ fderiv ℝ (fun v ↦ F v y) u d -
        fderiv ℝ (fun v ↦ G v y) u d) ≤ ENNReal.ofReal b) :
    ‖fderiv ℝ (fun v ↦ fderiv ℝ (fderiv ℝ (F v ∘ (A.chart i).symm)) (A.chart i x)) u d - H‖ ≤
      e + probeAtlasDerivativeConstant n N 2 * b := by
  have hdiff := atlas_native_hessian_response_difference_bound_of_originalC2
    A hA i hU F G hF hG u d hu x hx hb htail
  let DF := fderiv ℝ
    (fun v ↦ fderiv ℝ (fderiv ℝ (F v ∘ (A.chart i).symm)) (A.chart i x)) u d
  let DG := fderiv ℝ
    (fun v ↦ fderiv ℝ (fderiv ℝ (G v ∘ (A.chart i).symm)) (A.chart i x)) u d
  calc
    _ = ‖(DF - DG) + (DG - H)‖ := by congr 1; dsimp only [DF, DG]; abel
    _ ≤ ‖DF - DG‖ + ‖DG - H‖ := norm_add_le (DF - DG) (DG - H)
    _ ≤ probeAtlasDerivativeConstant n N 2 * b + e := add_le_add hdiff hmodel
    _ = _ := add_comm _ _

/-- The preceding actual-tail transfer in the original probe scale. A native
model error sigma*(eta+C*‖u‖) and an original C² tail of that same scale give
the required native response with the explicitly combined modulus and constant. -/
theorem atlas_native_hessian_response_scaled_bound_of_originalC2_tail
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    {U : Set P} (hU : IsOpen U) (F G : P → M → V)
    (hF : ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V) ∞
      (Function.uncurry F) (U ×ˢ univ))
    (hG : ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V) ∞
      (Function.uncurry G) (U ×ˢ univ))
    (u d : P) (hu : u ∈ U) (x : M) (hx : x ∈ A.support i)
    (H : E →L[ℝ] E →L[ℝ] V) (sigma etaModel etaTail CModel CTail : ℝ)
    (hsigma : 0 ≤ sigma) (hetaTail : 0 ≤ etaTail) (hCTail : 0 ≤ CTail)
    (hmodel : ‖fderiv ℝ
      (fun v ↦ fderiv ℝ (fderiv ℝ (G v ∘ (A.chart i).symm)) (A.chart i x)) u d - H‖ ≤
        sigma * (etaModel + CModel * ‖u‖))
    (htail : probeAtlasCj A 2
      (fun y ↦ fderiv ℝ (fun v ↦ F v y) u d -
        fderiv ℝ (fun v ↦ G v y) u d) ≤ ENNReal.ofReal (sigma * (etaTail + CTail * ‖u‖))) :
    ‖fderiv ℝ (fun v ↦ fderiv ℝ (fderiv ℝ (F v ∘ (A.chart i).symm)) (A.chart i x)) u d - H‖ ≤
      sigma * ((etaModel + probeAtlasDerivativeConstant n N 2 * etaTail) +
        (CModel + probeAtlasDerivativeConstant n N 2 * CTail) * ‖u‖) := by
  have h := atlas_native_hessian_response_bound_of_originalC2_tail A hA i hU F G hF hG
    u d hu x hx H (mul_nonneg hsigma (add_nonneg hetaTail (mul_nonneg hCTail (norm_nonneg u))))
    hmodel htail
  convert h using 1
  ring

end ActualFamily
end GlobalEmbedding.NormalPolar
