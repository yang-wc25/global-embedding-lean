import NormalPolar.FullResponseBounds
import Main.GeneralNativeProbeGap
import Main.GeneralProbeHessian

/-!
# Full original second-form response from actual native probe data

All three terms of the native product-rule bridge are retained. The principal
tensor is uniformly bounded on the original fixed atlas, the current Hessian
is bounded by the genuine original C³ budget, and the same constructed Q has
its parameter response derived from the genuine original C¹ budget.
-/

noncomputable section
open Set Filter Manifold
open scoped Topology ContDiff ENNReal

namespace GlobalEmbedding.Continuation
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade GlobalEmbedding.Offline GlobalEmbedding.NormalPolar
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ, E)

namespace GeneralNativeProbeData
variable {F₀ : M → EuclideanSpace ℝ (Fin N)}
    {hF₀ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F₀}
    {A : BufferedAtlas M (EuclideanSpace ℝ (Fin n))} {hA : IsSmoothBufferedAtlas A}
    {hcompact : ∀ i, IsCompact (A.support i)}
    {hcover : ∀ x, ∃ i, x ∈ A.support i}
    {hi₀ : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F₀ x)}
    {r : ℕ} {waves : Fin r → OpenSupportedLegalWave F₀ hF₀}

/-- The native data's C¹ field controls the actual parameter derivative of
its constructed Q, uniformly on the unchanged original atlas supports. -/
theorem exists_uniform_geometry_normal_response
    (d : GeneralNativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves) :
    ∃ CQ : ℝ, 0 < CQ ∧
      ∀ t, 0 < t → t < d.threshold → ∀ u a, ‖u‖ < d.radius →
        ∀ i z, z ∈ A.support i →
          ‖fderiv ℝ (fun v ↦ normalIdentificationOperator (n := n) F₀
            (d.geometry.map t v) (d.geometry.normalIdentification t v) z) u a‖ ≤
              CQ * (d.constant * t ^ (10 : ℕ) * ‖a‖) := by
  obtain ⟨CQ, hCQ, hbound⟩ := exists_uniform_actualProbeGeometry_normal_response_originalC1
    A hA hcompact F₀ hF₀ hi₀ d.reserve d.reserve_lt_one
  refine ⟨CQ, hCQ, ?_⟩
  intro t ht htt u a hu i z hz
  have hb : 0 ≤ d.constant * t ^ (10 : ℕ) * ‖a‖ :=
    mul_nonneg (mul_nonneg d.constant_nonneg (pow_nonneg ht.le _)) (norm_nonneg _)
  exact hbound d.map d.radius d.threshold d.radius_pos d.threshold_pos
    d.slice_smooth d.immersion d.joint_smooth d.metric d.projection_gap
    t ht htt u a hu i z hz _ hb (d.parameter_C1 t ht htt u hu a)

/-- The complete original second-form response for the same constructed
geometry, after a proved same-Q gap has been selected. The only response
input is the native Hessian response in the actual data. -/
theorem exists_secondForm_response_of_sameQ_gap [T2Space M]
    (d : GeneralNativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves)
    (gap : ℝ → ℝ) (hgap_nonneg : ∀ t, 0 ≤ gap t)
    (hgap_lim : Tendsto gap (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hgap : ∀ t, 0 < t → t < d.threshold → ∀ u, ‖u‖ < d.radius →
      ∀ i z, z ∈ A.support i →
        ‖normalIdentificationOperator (n := n) F₀ (d.geometry.map t u)
          (d.geometry.normalIdentification t u) z -
          (normalSpace (I := IM) F₀ z).starProjection‖ ≤ gap t) :
    ∃ Cresp : ℝ, 0 ≤ Cresp ∧ ∃ etaB : ℝ → ℝ,
      (∀ t, 0 ≤ etaB t) ∧ Tendsto etaB (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      ∀ t, 0 < t → t < d.threshold → ∀ u, ‖u‖ < d.radius →
        ∀ l b i z, z ∈ A.support i →
          ‖fderiv ℝ (fun v ↦ probeTensorInFrame (probeAtlasFrame A i z)
              (identifiedTrueSecondForm (n := n) F₀ (d.geometry.map t v)
                (d.geometry.slice_smooth t v) (d.geometry.normalIdentification t v) z))
              u (Pi.single (l, b) 1) -
            (t ^ ((44 : ℝ) / 5) * probeTrig b (d.weight l * (waves l).phase z /
              t ^ ((6 : ℝ) / 5))) •
              probeTensorInFrame (probeAtlasFrame A i z) ((waves l).tensor z)‖ ≤
            t ^ ((44 : ℝ) / 5) * (etaB t + Cresp * ‖u‖) := by
  obtain ⟨B, hB, hBbound⟩ := exists_uniform_general_wave_tensor_in_frame_bound A hA hcompact waves
  obtain ⟨CQ, hCQ, hQbound⟩ := d.exists_uniform_geometry_normal_response
  let L := actualHessianLiftConstant E V
  let HC := L * (probeAtlasDerivativeConstant n N 2 * d.constant)
  let D := (CQ * d.constant) * HC
  have hL : 0 ≤ L := actualHessianLiftConstant_nonneg
  have hHC : 0 ≤ HC :=
    mul_nonneg hL (mul_nonneg (probeAtlasDerivativeConstant_nonneg n N 2) d.constant_nonneg)
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg hCQ.le d.constant_nonneg) hHC
  refine ⟨L * d.constant, mul_nonneg hL d.constant_nonneg,
    fullSecondFormModulus L B D d.etaH gap,
    fullSecondFormModulus_nonneg L B D hL hB.le hD d.etaH gap d.etaH_nonneg hgap_nonneg,
    fullSecondFormModulus_tendsto L B D d.etaH gap d.etaH_tendsto hgap_lim, ?_⟩
  intro t ht htt u hu l b i z hz
  let sigma := t ^ ((44 : ℝ) / 5)
  let theta := d.weight l * (waves l).phase z / t ^ ((6 : ℝ) / 5)
  let coefficient := sigma * probeTrig b theta
  have hsigma : 0 ≤ sigma := Real.rpow_nonneg ht.le _
  have hten : 0 ≤ t ^ (10 : ℕ) := pow_nonneg ht.le _
  have hc : ‖coefficient‖ ≤ sigma := by
    dsimp only [coefficient]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hsigma]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (probeTrig_abs_le_one b theta) hsigma
  have hprincipal :
      ‖coefficient • probeTensorInFrame (probeAtlasFrame A i z) ((waves l).tensor z)‖ ≤
        sigma * B := by
    rw [norm_smul]
    exact mul_le_mul hc (hBbound l i z hz) (norm_nonneg _) hsigma
  have hQ := hQbound t ht htt u (Pi.single (l, b) 1) hu i z hz
  simp only [Pi.norm_single, norm_one, mul_one] at hQ
  have hH : ‖probeAtlasSecondJet A (d.geometry.map t u) i z‖ ≤ HC :=
    probeAtlasSecondJet_norm_le_originalC3 A hA (d.map t u) (d.slice_smooth t u)
      d.constant d.constant_nonneg (d.spatial_C3 t ht htt u hu) i z hz
  have hraw := mul_le_mul_of_nonneg_left (d.native_hessian_response t ht htt u hu l b i z hz) hL
  have hgap_term := mul_le_mul (hgap t ht htt u hu i z hz) hprincipal
    (norm_nonneg _) (hgap_nonneg t)
  have hQ_term := mul_le_mul hQ hH (norm_nonneg _)
    (mul_nonneg hCQ.le (mul_nonneg d.constant_nonneg hten))
  have hnative := generalProbeGeometry_identified_secondForm_response_native_bound d.geometry (waves l)
    A hA i t ht htt u (Pi.single (l, b) 1) hu z (hA.support_subset i hz) coefficient
  have hbound := hnative.trans (add_le_add (add_le_add hraw hgap_term) hQ_term)
  calc
    _ ≤ L * (sigma * (d.etaH t + d.constant * ‖u‖)) +
        gap t * (sigma * B) + (CQ * (d.constant * t ^ (10 : ℕ))) * HC := hbound
    _ = L * (sigma * (d.etaH t + d.constant * ‖u‖)) +
        gap t * (sigma * B) + D * t ^ (10 : ℕ) := by dsimp only [D]; ring
    _ = _ := fullSecondFormModulus_scaled L B D d.constant ‖u‖ d.etaH gap t ht

/-- Direct output for the original probe contract. The same-Q gap is
constructed from this actual family's original C² budget, so neither a gap
nor an identified-form response occurs among the input fields. -/
theorem exists_secondForm_response [T2Space M]
    (d : GeneralNativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves) :
    ∃ Cresp : ℝ, 0 ≤ Cresp ∧ ∃ etaB : ℝ → ℝ,
      (∀ t, 0 ≤ etaB t) ∧ Tendsto etaB (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      ∀ t, 0 < t → t < d.threshold → ∀ u, ‖u‖ < d.radius →
        ∀ l b i z, z ∈ A.support i →
          ‖fderiv ℝ (fun v ↦ probeTensorInFrame (probeAtlasFrame A i z)
              (identifiedTrueSecondForm (n := n) F₀ (d.geometry.map t v)
                (d.geometry.slice_smooth t v) (d.geometry.normalIdentification t v) z))
              u (Pi.single (l, b) 1) -
            (t ^ ((44 : ℝ) / 5) * probeTrig b (d.weight l * (waves l).phase z /
              t ^ ((6 : ℝ) / 5))) •
              probeTensorInFrame (probeAtlasFrame A i z) ((waves l).tensor z)‖ ≤
            t ^ ((44 : ℝ) / 5) * (etaB t + Cresp * ‖u‖) :=
  d.exists_secondForm_response_of_sameQ_gap d.normalGap d.normalGap_nonneg
    d.normalGap_tendsto d.normalGap_bound

end GeneralNativeProbeData
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.GeneralNativeProbeData.exists_secondForm_response
