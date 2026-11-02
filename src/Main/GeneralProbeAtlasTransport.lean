import Main.GeneralProbeAtlasNorms
import Main.GeneralProbeAtlasResponse

/-!
# Change the atlas of the SAME complete actual probe family

Actual compact coordinate geometry transfers every field of the original
`GeneralExactProbeFamily`. The full `ProbeGeometry`, weights, etaV, radius and scale
interval are preserved literally. Only one common constant and etaB are
enlarged. The same chosen normal gap is transported separately.

This construction consumes an existing complete family; it does not supply
the missing repaired family or weaken any original probes field.
-/

noncomputable section
open Bundle Filter Manifold Set
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
open Paper GlobalEmbedding.Offline GlobalEmbedding.Upgrade SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M] [T2Space M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The same complete family on another actual compact smooth atlas. The
chosen geometric constants are independent of t, u, the direction and label.
The old atlas supports must cover; the new supports need no interior cover. -/
def GeneralExactProbeFamily.changeAtlas
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} {r : ℕ} {waves : Fin r → OpenSupportedLegalWave F₀ hF₀}
    (probe : GeneralExactProbeFamily F₀ hF₀ A waves)
    (B : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
    (hAc : ∀ i, IsCompact (A.support i)) (hBc : ∀ j, IsCompact (B.support j))
    (hcoverA : ∀ x : M, ∃ i, x ∈ A.support i) : GeneralExactProbeFamily F₀ hF₀ B waves := by
  let normExist := probe.exists_changeAtlas_norm_constant B hA hB hAc hBc hcoverA
  let Cnorm := Classical.choose normExist
  have hnorm := Classical.choose_spec normExist
  let responseExist := exists_uniform_general_actual_probe_response_atlas_transfer
    (N := N) A B hA hB hAc hBc hcoverA
  let R := max 1 (Classical.choose responseExist)
  have hresponse := Classical.choose_spec responseExist
  have hRbase_le : Classical.choose responseExist ≤ R := le_max_right _ _
  let Cnew := max Cnorm (R * probe.constant)
  have hnorm_le : Cnorm ≤ Cnew := le_max_left _ _
  have hresponse_le : R * probe.constant ≤ Cnew := le_max_right _ _
  have hconstant_le : probe.constant ≤ Cnew := hnorm.1.trans hnorm_le
  have hconstant_nonneg : 0 ≤ Cnew := probe.constant_nonneg.trans hconstant_le
  have hRnonneg : 0 ≤ R := zero_le_one.trans (le_max_left _ _)
  refine {
    toProbeGeometry := probe.toProbeGeometry
    weight := probe.weight
    weight_pos := probe.weight_pos
    distinct_on_overlap := probe.distinct_on_overlap
    constant := Cnew
    constant_nonneg := hconstant_nonneg
    etaB := fun t ↦ R * probe.etaB t
    etaV := probe.etaV
    etaB_nonneg := fun t ↦ mul_nonneg hRnonneg (probe.etaB_nonneg t)
    etaV_nonneg := probe.etaV_nonneg
    etaB_tendsto := ?_
    etaV_tendsto := probe.etaV_tendsto
    closeness := ?_
    spatial_C3 := ?_
    parameter_C1 := ?_
    parameter_C2 := ?_
    secondForm_response := ?_
    value_response := ?_ }
  · simpa only [mul_zero] using probe.etaB_tendsto.const_mul R
  · intro t ht htt u hu
    exact ((hnorm.2.2 t ht htt u hu).1).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hnorm_le (Real.rpow_nonneg ht.le _)))
  · intro t ht htt u hu
    exact ((hnorm.2.2 t ht htt u hu).2.1).trans (ENNReal.ofReal_le_ofReal hnorm_le)
  · intro t ht htt u hu d
    exact ((hnorm.2.2 t ht htt u hu).2.2.1 d).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hnorm_le (pow_nonneg ht.le _)) (norm_nonneg d)))
  · intro t ht htt u hu d
    exact ((hnorm.2.2 t ht htt u hu).2.2.2 d).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hnorm_le (Real.rpow_nonneg ht.le _)) (norm_nonneg d)))
  · intro t ht htt u hu l b j z hz
    have hraw := hresponse.2 F₀ hF₀ r probe.toProbeGeometry (waves l) t ht htt u
      (Pi.single (l, b) 1) hu
      (t ^ ((44 : ℝ) / 5) * probeTrig b
        (probe.weight l * (waves l).phase z / t ^ ((6 : ℝ) / 5)))
      (t ^ ((44 : ℝ) / 5) * (probe.etaB t + probe.constant * ‖u‖)) j z hz
      (fun i hi ↦ probe.secondForm_response t ht htt u hu l b i z hi)
    have herror_nonneg : 0 ≤ t ^ ((44 : ℝ) / 5) * (probe.etaB t + probe.constant * ‖u‖) :=
      mul_nonneg (Real.rpow_nonneg ht.le _) (add_nonneg (probe.etaB_nonneg t)
        (mul_nonneg probe.constant_nonneg (norm_nonneg u)))
    have h := hraw.trans (mul_le_mul_of_nonneg_right hRbase_le herror_nonneg)
    apply h.trans
    calc
      R * (t ^ ((44 : ℝ) / 5) * (probe.etaB t + probe.constant * ‖u‖)) =
          t ^ ((44 : ℝ) / 5) * (R * probe.etaB t + (R * probe.constant) * ‖u‖) := by ring
      _ ≤ t ^ ((44 : ℝ) / 5) * (R * probe.etaB t + Cnew * ‖u‖) :=
        mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (mul_le_mul_of_nonneg_right hresponse_le (norm_nonneg u)))
          (Real.rpow_nonneg ht.le _)
  · intro t ht htt u hu l b z
    exact (probe.value_response t ht htt u hu l b z).trans
      (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right hconstant_le (norm_nonneg u)))
        (Real.rpow_nonneg ht.le _))

@[simp] theorem GeneralExactProbeFamily.changeAtlas_toProbeGeometry
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} {r : ℕ} {waves : Fin r → OpenSupportedLegalWave F₀ hF₀}
    (probe : GeneralExactProbeFamily F₀ hF₀ A waves)
    (B : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
    (hAc : ∀ i, IsCompact (A.support i)) (hBc : ∀ j, IsCompact (B.support j))
    (hcoverA : ∀ x : M, ∃ i, x ∈ A.support i) :
    (probe.changeAtlas B hA hB hAc hBc hcoverA).toProbeGeometry = probe.toProbeGeometry := rfl

@[simp] theorem GeneralExactProbeFamily.changeAtlas_map
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} {r : ℕ} {waves : Fin r → OpenSupportedLegalWave F₀ hF₀}
    (probe : GeneralExactProbeFamily F₀ hF₀ A waves)
    (B : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
    (hAc : ∀ i, IsCompact (A.support i)) (hBc : ∀ j, IsCompact (B.support j))
    (hcoverA : ∀ x : M, ∃ i, x ∈ A.support i) :
    (probe.changeAtlas B hA hB hAc hBc hcoverA).map = probe.map := rfl

@[simp] theorem GeneralExactProbeFamily.changeAtlas_normalIdentification
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} {r : ℕ} {waves : Fin r → OpenSupportedLegalWave F₀ hF₀}
    (probe : GeneralExactProbeFamily F₀ hF₀ A waves)
    (B : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
    (hAc : ∀ i, IsCompact (A.support i)) (hBc : ∀ j, IsCompact (B.support j))
    (hcoverA : ∀ x : M, ∃ i, x ∈ A.support i) :
    (probe.changeAtlas B hA hB hAc hBc hcoverA).normalIdentification =
      probe.normalIdentification := rfl

@[simp] theorem GeneralExactProbeFamily.changeAtlas_weight
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} {r : ℕ} {waves : Fin r → OpenSupportedLegalWave F₀ hF₀}
    (probe : GeneralExactProbeFamily F₀ hF₀ A waves)
    (B : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
    (hAc : ∀ i, IsCompact (A.support i)) (hBc : ∀ j, IsCompact (B.support j))
    (hcoverA : ∀ x : M, ∃ i, x ∈ A.support i) :
    (probe.changeAtlas B hA hB hAc hBc hcoverA).weight = probe.weight := rfl

@[simp] theorem GeneralExactProbeFamily.changeAtlas_etaV
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} {r : ℕ} {waves : Fin r → OpenSupportedLegalWave F₀ hF₀}
    (probe : GeneralExactProbeFamily F₀ hF₀ A waves)
    (B : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
    (hAc : ∀ i, IsCompact (A.support i)) (hBc : ∀ j, IsCompact (B.support j))
    (hcoverA : ∀ x : M, ∃ i, x ∈ A.support i) :
    (probe.changeAtlas B hA hB hAc hBc hcoverA).etaV = probe.etaV := rfl

#print axioms GeneralExactProbeFamily.changeAtlas
#print axioms GeneralExactProbeFamily.changeAtlas_toProbeGeometry

end GlobalEmbedding.Continuation
