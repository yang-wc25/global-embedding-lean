import NormalPolar.IdentificationTransportControls
import NormalPolar.IdentificationTransportImmersion
import NormalPolar.ProbeIntegrationTotalGap

/-!
# Actual canonical data for safely replacing a probe identification

The new Q below is computed from the actual normal projections of the same
map. Its global existence follows from the original total normal isometries,
its same-Q gap follows from the original C² budget, and its true parameter
response follows from the original C¹ budget. None of those new-Q outputs is
an assumption of the canonical reselection construction.
-/

noncomputable section
open Set Filter Manifold
open scoped Topology ContDiff ENNReal

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade GlobalEmbedding.Offline

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The actual total polar identification of the original probe maps.
No new map, parameter domain or global immersion premise is supplied. -/
def canonicalNormalIdentificationOfProbe
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (p : ExactProbeFamily F₀ hF₀ A waves)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (t : ℝ) (u : ProbeParameters r) (z : M) :
    normalSpace (I := IM) (p.map t u) z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z :=
  actualImmersionNormalIdentification F₀ (p.map t u) hi₀
    (probeGeometry_all_slice_immersion p.toProbeGeometry hi₀ t u) z

/-- The canonical actual field is jointly smooth on exactly the old
admitted open domain once the true projections satisfy the stated reserve. -/
theorem canonicalNormalIdentificationOfProbe_smooth
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (p : ExactProbeFamily F₀ hF₀ A waves)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (hreserve : ∀ t, 0 < t → t < p.threshold → ∀ u, ‖u‖ < p.radius → ∀ x,
      ‖(normalSpace (I := IM) F₀ x).starProjection -
        (normalSpace (I := IM) (p.map t u) x).starProjection‖ < 1) :
    ∀ t, 0 < t → t < p.threshold →
      ContMDiffOn ((𝓘(ℝ, ProbeParameters r)).prod IM) 𝓘(ℝ, V →L[ℝ] V) ∞
        (fun w : ProbeParameters r × M ↦ normalIdentificationOperator (n := n) F₀
          (p.map t w.1) (canonicalNormalIdentificationOfProbe p hi₀ t w.1) w.2)
        (Metric.ball 0 p.radius ×ˢ univ) :=
  (canonicalProbeGeometryOfProbeGeometry p.toProbeGeometry hF₀ hi₀ hreserve).normalIdentification_smooth

/-- The new actual Q has a uniform same-Q gap on the unchanged original
parameter ball and atlas supports, derived solely from the old C² field. -/
theorem exists_canonicalNormalIdentificationOfProbe_gap
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (p : ExactProbeFamily F₀ hF₀ A waves)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x)) :
    ∃ g : ℝ → ℝ, (∀ t, 0 ≤ g t) ∧ Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      ∀ t, 0 < t → t < p.threshold → ∀ u, ‖u‖ < p.radius →
        ∀ i x, x ∈ A.support i →
          ‖normalIdentificationOperator (n := n) F₀ (p.map t u)
            (canonicalNormalIdentificationOfProbe p hi₀ t u) x -
            (normalSpace (I := IM) F₀ x).starProjection‖ ≤ g t := by
  let budget := fun t : ℝ ↦ p.constant * |t| ^ ((44 : ℝ) / 5)
  have hnonneg (t : ℝ) : 0 ≤ budget t :=
    mul_nonneg p.constant_nonneg (Real.rpow_nonneg (abs_nonneg t) _)
  have hlim : Tendsto budget (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ ↦ |t| ^ ((44 : ℝ) / 5)) :=
      (Real.continuous_rpow_const (by norm_num : 0 ≤ (44 : ℝ) / 5)).comp continuous_abs
    have hp : Tendsto (fun t : ℝ ↦ |t| ^ ((44 : ℝ) / 5))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using hc.continuousAt.tendsto.mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from inf_le_left)
    simpa only [mul_zero] using hp.const_mul p.constant
  obtain ⟨g, hg, hglim, hbound⟩ := exists_total_sameQ_gap_of_actual_maps_originalC2
    F₀ hF₀ hi₀ p.map (probeGeometry_all_slice_immersion p.toProbeGeometry hi₀)
    (Set.Ioo 0 p.threshold) (Metric.ball 0 p.radius)
    (fun t _ u _ ↦ p.slice_smooth t u) A hA hcompact
    (fun t ht u hu ↦ p.metric t ht.1 ht.2 u (by simpa using hu))
    budget hnonneg hlim (fun t ht u hu ↦ by
      change probeAtlasCj A 2 (p.map t u - F₀) ≤
        ENNReal.ofReal (p.constant * |t| ^ ((44 : ℝ) / 5))
      rw [abs_of_pos ht.1]
      exact p.closeness t ht.1 ht.2 u (by simpa using hu))
  refine ⟨g, hg, hglim, ?_⟩
  intro t ht htt u hu i x hx
  exact hbound t ⟨ht, htt⟩ u (by simpa using hu) i x hx

/-- The new actual Q parameter derivative is controlled by the original
C¹ field. The uniform reserve is genuine projection data on the old domain. -/
theorem exists_canonicalNormalIdentificationOfProbe_response
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (p : ExactProbeFamily F₀ hF₀ A waves)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (q : ℝ) (hq : q < 1)
    (hreserve : ∀ t, 0 < t → t < p.threshold → ∀ u, ‖u‖ < p.radius → ∀ x,
      ‖(normalSpace (I := IM) F₀ x).starProjection -
        (normalSpace (I := IM) (p.map t u) x).starProjection‖ ≤ q) :
    ∃ C : ℝ, 0 < C ∧
      ∀ t, 0 < t → t < p.threshold → ∀ u d, ‖u‖ < p.radius →
        ∀ i x, x ∈ A.support i →
          ‖fderiv ℝ (fun v ↦ normalIdentificationOperator (n := n) F₀ (p.map t v)
            (canonicalNormalIdentificationOfProbe p hi₀ t v) x) u d‖ ≤
              C * (p.constant * t ^ (10 : ℕ) * ‖d‖) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_actualProbeGeometry_normal_response_originalC1
    A hA hcompact F₀ hF₀ hi₀ q hq
  refine ⟨C, hC, ?_⟩
  intro t ht htt u d hu i x hx
  have hb : 0 ≤ p.constant * t ^ (10 : ℕ) * ‖d‖ :=
    mul_nonneg (mul_nonneg p.constant_nonneg (pow_nonneg ht.le _)) (norm_nonneg _)
  exact hbound p.map p.radius p.threshold p.radius_pos p.threshold_pos
    p.slice_smooth (probeGeometry_all_slice_immersion p.toProbeGeometry hi₀)
    p.joint_smooth p.metric hreserve t ht htt u d hu i x hx _ hb
    (p.parameter_C1 t ht htt u hu d)

end GlobalEmbedding.NormalPolar
