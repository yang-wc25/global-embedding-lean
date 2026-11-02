import Main.GeneralNativeProbeData

/-!
# The same-Q gap derived from the actual native probe input

The nonnegative global budget extends the original positive-scale expression
with an absolute value. On every admitted scale it is exactly the original
budget. The gap below is then selected from the already proved actual-map
theorem; no normal-operator estimate is added to GeneralNativeProbeData.
-/

noncomputable section
open Set Filter Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.Continuation
open GlobalEmbedding.Upgrade GlobalEmbedding.NormalPolar

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

/-- A nonnegative total extension of the original positive-scale C² budget. -/
def closenessBudget (d : GeneralNativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves)
    (t : ℝ) : ℝ := d.constant * |t| ^ ((44 : ℝ) / 5)

theorem closenessBudget_nonneg
    (d : GeneralNativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves) (t : ℝ) :
    0 ≤ d.closenessBudget t :=
  mul_nonneg d.constant_nonneg (Real.rpow_nonneg (abs_nonneg t) _)

theorem closenessBudget_eq_of_pos
    (d : GeneralNativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves)
    {t : ℝ} (ht : 0 < t) :
    d.closenessBudget t = d.constant * t ^ ((44 : ℝ) / 5) := by
  simp only [closenessBudget, abs_of_pos ht]

theorem closenessBudget_tendsto
    (d : GeneralNativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves) :
    Tendsto d.closenessBudget (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h := ((Real.continuous_rpow_const (q := (44 : ℝ) / 5)
    (by positivity)).comp continuous_abs).tendsto (0 : ℝ)
  have hp : Tendsto (fun t : ℝ ↦ |t| ^ ((44 : ℝ) / 5)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def, abs_zero, Real.zero_rpow (by norm_num : (44 : ℝ) / 5 ≠ 0)] using
      h.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  change Tendsto (fun t : ℝ ↦ d.constant * |t| ^ ((44 : ℝ) / 5)) (𝓝[>] (0 : ℝ)) (𝓝 0)
  simpa only [mul_zero] using hp.const_mul d.constant

/-- The required uniform same-Q gap is a theorem about the geometry actually
constructed from d. All its quantitative input is the original C² field. -/
theorem exists_sameQ_gap
    (d : GeneralNativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves) :
    ∃ g : ℝ → ℝ, (∀ t, 0 ≤ g t) ∧ Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      ∀ t, 0 < t → t < d.threshold → ∀ u, ‖u‖ < d.radius →
        ∀ i x, x ∈ A.support i →
          ‖normalIdentificationOperator (n := n) F₀ (d.geometry.map t u)
            (d.geometry.normalIdentification t u) x -
            (normalSpace (I := IM) F₀ x).starProjection‖ ≤ g t := by
  obtain ⟨g, hg, hlim, hbound⟩ := exists_total_sameQ_gap_of_actual_maps_originalC2
    F₀ hF₀ hi₀ d.map d.immersion (Set.Ioo 0 d.threshold) (Metric.ball 0 d.radius)
    (fun t _ u _ ↦ d.slice_smooth t u) A hA hcompact
    (fun t ht u hu ↦ d.metric t ht.1 ht.2 u (by simpa using hu))
    d.closenessBudget d.closenessBudget_nonneg d.closenessBudget_tendsto
    (fun t ht u hu ↦ by
      rw [d.closenessBudget_eq_of_pos ht.1]
      exact d.closeness t ht.1 ht.2 u (by simpa using hu))
  refine ⟨g, hg, hlim, ?_⟩
  intro t ht htt u hu i x hx
  exact hbound t ⟨ht, htt⟩ u (by simpa using hu) i x hx

/-- A selected modulus for this actual geometry, chosen from a proved bound. -/
def normalGap (d : GeneralNativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves) : ℝ → ℝ :=
  d.exists_sameQ_gap.choose

theorem normalGap_nonneg
    (d : GeneralNativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves) (t : ℝ) :
    0 ≤ d.normalGap t := d.exists_sameQ_gap.choose_spec.1 t

theorem normalGap_tendsto
    (d : GeneralNativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves) :
    Tendsto d.normalGap (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  d.exists_sameQ_gap.choose_spec.2.1

theorem normalGap_bound
    (d : GeneralNativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves)
    (t : ℝ) (ht : 0 < t) (htt : t < d.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < d.radius)
    (i : Fin A.count) (x : M) (hx : x ∈ A.support i) :
    ‖normalIdentificationOperator (n := n) F₀ (d.geometry.map t u)
      (d.geometry.normalIdentification t u) x -
      (normalSpace (I := IM) F₀ x).starProjection‖ ≤ d.normalGap t :=
  d.exists_sameQ_gap.choose_spec.2.2 t ht htt u hu i x hx

/-- The modulus controls the same explicit polar formula on the original
domain, for consumers using the native-response formula directly. -/
theorem polarGap_bound
    (d : GeneralNativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves)
    (t : ℝ) (ht : 0 < t) (htt : t < d.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < d.radius)
    (i : Fin A.count) (x : M) (hx : x ∈ A.support i) :
    ‖actualPolarOperator (normalSpace (I := IM) F₀ x).starProjection
      (normalSpace (I := IM) (d.map t u) x).starProjection -
      (normalSpace (I := IM) F₀ x).starProjection‖ ≤ d.normalGap t := by
  have h := d.normalGap_bound t ht htt u hu i x hx
  change ‖normalIdentificationOperator (n := n) F₀ (d.map t u)
    (actualImmersionNormalIdentification F₀ (d.map t u) hi₀ (d.immersion t u)) x -
    (normalSpace (I := IM) F₀ x).starProjection‖ ≤ d.normalGap t at h
  rw [actualImmersionNormalIdentification_operator F₀ (d.map t u) hi₀ (d.immersion t u) x
    ((d.projection_gap t ht htt u hu x).trans_lt d.reserve_lt_one)] at h
  exact h

end GeneralNativeProbeData
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.GeneralNativeProbeData.exists_sameQ_gap
#print axioms GlobalEmbedding.Continuation.GeneralNativeProbeData.normalGap_bound
