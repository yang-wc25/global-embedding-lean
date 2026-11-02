import Round2.AtlasProbeTransportParameter
import Main.GeneralExactProbeFamily

/-!
# Transfer all original map and parameter norms of one actual probe family

The maps and parameter responses below are literally those of the supplied
complete family. Actual finite smooth coordinate transitions provide the
three norm constants. A single enlarged constant controls displacement C²,
spatial C³ and both parameter C¹/C² bounds on the new atlas, with the original
radius and small-scale interval unchanged.
-/

noncomputable section
open Bundle Filter Manifold Set
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
open Paper GlobalEmbedding.Offline GlobalEmbedding.Upgrade

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M] [T2Space M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- A single scalar transfers the four literal original norm bounds of the
same complete probe family. No new probe map, parameter derivative or global
smoothness premise for a response field is supplied. -/
theorem GeneralExactProbeFamily.exists_changeAtlas_norm_constant
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} {r : ℕ} {waves : Fin r → OpenSupportedLegalWave F₀ hF₀}
    (probe : GeneralExactProbeFamily F₀ hF₀ A waves)
    (B : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
    (hAc : ∀ i, IsCompact (A.support i)) (hBc : ∀ j, IsCompact (B.support j))
    (hcoverA : ∀ x : M, ∃ i, x ∈ A.support i) :
    ∃ C : ℝ, probe.constant ≤ C ∧ 0 ≤ C ∧
      ∀ t, 0 < t → t < probe.threshold → ∀ u, ‖u‖ < probe.radius →
        probeAtlasCj B 2 (probe.map t u - F₀) ≤ ENNReal.ofReal (C * t ^ ((44 : ℝ) / 5)) ∧
        probeAtlasCj B 3 (probe.map t u) ≤ ENNReal.ofReal C ∧
        (∀ d, probeAtlasCj B 1 (fun x ↦ fderiv ℝ (fun v ↦ probe.map t v x) u d) ≤
          ENNReal.ofReal (C * t ^ (10 : ℕ) * ‖d‖)) ∧
        (∀ d, probeAtlasCj B 2 (fun x ↦ fderiv ℝ (fun v ↦ probe.map t v x) u d) ≤
          ENNReal.ofReal (C * t ^ ((44 : ℝ) / 5) * ‖d‖)) := by
  obtain ⟨K₁, hK₁, htransfer₁⟩ := exists_probeAtlasCj_transfer_bound_of_coordinate_smooth
    (N := N) 1 A B hA hB hAc hBc hcoverA
  obtain ⟨K₂, hK₂, htransfer₂⟩ := exists_probeAtlasCj_transfer_bound_of_coordinate_smooth
    (N := N) 2 A B hA hB hAc hBc hcoverA
  obtain ⟨K₃, hK₃, htransfer₃⟩ := exists_probeAtlasCj_transfer_bound_of_coordinate_smooth
    (N := N) 3 A B hA hB hAc hBc hcoverA
  let L := max 1 (max K₁ (max K₂ K₃))
  have hLone : 1 ≤ L := le_max_left _ _
  have hL₁ : K₁ ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have hL₂ : K₂ ≤ L := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hL₃ : K₃ ≤ L := (le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  let C := L * probe.constant
  have hCold : probe.constant ≤ C := by
    exact (one_mul probe.constant).symm ▸ mul_le_mul_of_nonneg_right hLone probe.constant_nonneg
  have hCnonneg : 0 ≤ C := probe.constant_nonneg.trans hCold
  refine ⟨C, hCold, hCnonneg, ?_⟩
  intro t ht htt u hu
  have hsigma : 0 ≤ t ^ ((44 : ℝ) / 5) := Real.rpow_nonneg ht.le _
  have ht10 : 0 ≤ t ^ (10 : ℕ) := pow_nonneg ht.le _
  have hdisplacement : ContMDiff IM 𝓘(ℝ, V) ∞ (probe.map t u - F₀) :=
    (probe.slice_smooth t u).sub hF₀
  have hclose := htransfer₂ (probe.map t u - F₀)
    (probeAtlas_coordinate_smooth A hA _ hdisplacement)
    (probeAtlas_coordinate_smooth B hB _ hdisplacement)
    (probe.constant * t ^ ((44 : ℝ) / 5)) (mul_nonneg probe.constant_nonneg hsigma)
    (probe.closeness t ht htt u hu)
  have hclose' : probeAtlasCj B 2 (probe.map t u - F₀) ≤
      ENNReal.ofReal (L * (probe.constant * t ^ ((44 : ℝ) / 5))) :=
    hclose.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hL₂ (mul_nonneg probe.constant_nonneg hsigma)))
  have hspatial := htransfer₃ (probe.map t u)
    (probeAtlas_coordinate_smooth A hA _ (probe.slice_smooth t u))
    (probeAtlas_coordinate_smooth B hB _ (probe.slice_smooth t u))
    probe.constant probe.constant_nonneg (probe.spatial_C3 t ht htt u hu)
  refine ⟨?_, hspatial.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hL₃ probe.constant_nonneg)), ?_, ?_⟩
  · simpa only [C, mul_assoc] using hclose'
  · intro d
    have hb : 0 ≤ probe.constant * t ^ (10 : ℕ) * ‖d‖ :=
      mul_nonneg (mul_nonneg probe.constant_nonneg ht10) (norm_nonneg d)
    have h := htransfer₁ (fun x ↦ fderiv ℝ (fun v ↦ probe.map t v x) u d)
      (fun i ↦ probe.toProbeGeometry.parameter_response_coordinate_smooth A hA i t ht htt u d hu)
      (fun j ↦ probe.toProbeGeometry.parameter_response_coordinate_smooth B hB j t ht htt u d hu)
      (probe.constant * t ^ (10 : ℕ) * ‖d‖) hb (probe.parameter_C1 t ht htt u hu d)
    have h' := h.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hL₁ hb))
    simpa only [C, mul_assoc] using h'
  · intro d
    have hb : 0 ≤ probe.constant * t ^ ((44 : ℝ) / 5) * ‖d‖ :=
      mul_nonneg (mul_nonneg probe.constant_nonneg hsigma) (norm_nonneg d)
    have h := htransfer₂ (fun x ↦ fderiv ℝ (fun v ↦ probe.map t v x) u d)
      (fun i ↦ probe.toProbeGeometry.parameter_response_coordinate_smooth A hA i t ht htt u d hu)
      (fun j ↦ probe.toProbeGeometry.parameter_response_coordinate_smooth B hB j t ht htt u d hu)
      (probe.constant * t ^ ((44 : ℝ) / 5) * ‖d‖) hb (probe.parameter_C2 t ht htt u hu d)
    have h' := h.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hL₂ hb))
    simpa only [C, mul_assoc] using h'

#print axioms GeneralExactProbeFamily.exists_changeAtlas_norm_constant

end GlobalEmbedding.Continuation
