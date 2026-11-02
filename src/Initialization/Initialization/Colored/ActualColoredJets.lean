import Initialization.Colored.ActualRateRows
import Initialization.Colored.PullbackReferenceJets

/-!
# Actual colored sphere jets, with no geometric or derivative-budget assumptions

The cutoffs, phases, coordinate maps and normalized coframe are all the actual
ones constructed from the compact source and original metric. The fixed
reference sequence and the full K⁻¹+K/T error sequence are chosen before K,T.
This is the analytic producer used by the selector, metric and phase consumers.
-/

noncomputable section
open Set Function Filter Metric Manifold IsManifold Bundle
open scoped ContDiff Topology Manifold

namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M] [CompactSpace M]

variable (G : PreparedCharts M n)
  (g : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
    (EuclideanSpace ℝ (Fin n))
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _))
  (f : FullTangentFrame 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M := M) n)

/-- The literal native sphere argument, in the actual fixed-radius scale chart. -/
def actualColoredSource {K T : ℝ} (F : ChartCutoffFamily G K)
    (Q : ChartCutoffFamily G T) (hT : 1 ≤ T) (p : Fin Q.count) :
    EuclideanSpace ℝ (Fin n) → FreeHopfProduct (fun _ : Fin n ↦ G.palette) :=
  preparedColoredProduct F (preparedCoframe G g f) T ∘ ((Q.boundedAtlas hT).chart p).symm

@[simp] theorem actualColoredSource_ambient {K T : ℝ}
    (F : ChartCutoffFamily G K) (Q : ChartCutoffFamily G T) (hT : 1 ≤ T) (p : Fin Q.count) :
    selectorSourceAmbient (fun _ : Fin n ↦ G.palette) (actualColoredSource G g f F Q hT p) =
      fun y l ↦ coloredAmbient F.color F.cutoff
        (preparedFrozenPhase F (preparedCoframe G g f) l) T
        (((Q.boundedAtlas hT).chart p).symm y) := rfl

theorem actualColoredSource_ambient_contDiffOn {K T : ℝ}
    (F : ChartCutoffFamily G K) (Q : ChartCutoffFamily G T) (hT : 1 ≤ T) (p : Fin Q.count) :
    ContDiffOn ℝ ∞
      (selectorSourceAmbient (fun _ : Fin n ↦ G.palette) (actualColoredSource G g f F Q hT p))
      (ball (0 : EuclideanSpace ℝ (Fin n)) G.scaleRadius) := by
  rw [actualColoredSource_ambient]
  apply contDiffOn_pi.mpr
  intro l
  have hfactor := coloredAmbient_contMDiff (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
    F.color F.cutoff (preparedFrozenPhase F (preparedCoframe G g f) l) T
    F.cutoff_smooth (preparedFrozenPhase_contMDiffAt F (preparedCoframe G g f) l)
  exact (hfactor.comp_contMDiffOn
    (contMDiffOn_symm_of_mem_maximalAtlas ((Q.boundedAtlas_smooth hT).chart_mem p))).contDiffOn

/-- The same selected map in this chart is exactly S of the actual sphere
argument; no alternate local construction is substituted. -/
theorem preparedSelectorMap_pullback_eq_source {K T : ℝ} {V : Type*}
    (S : FreeHopfProduct (fun _ : Fin n ↦ G.palette) → V)
    (F : ChartCutoffFamily G K) (Q : ChartCutoffFamily G T) (hT : 1 ≤ T) (p : Fin Q.count) :
    preparedSelectorMap S F (preparedCoframe G g f) T ∘ ((Q.boundedAtlas hT).chart p).symm =
      S ∘ actualColoredSource G g f F Q hT p := rfl

/-- Actual all-order reference and first-error bounds, now generated from the
compact source and original metric. There are no cutoff, phase, transition,
overlap, denominator, smoothness or derivative-budget premises. -/
theorem exists_actualColoredSource_jet_bounds :
    ∃ (B A : ℕ → ℝ), (∀ j, 0 ≤ B j) ∧ (∀ j, 0 ≤ A j) ∧
      ∀ (K T : ℝ) (hK : 1 ≤ K) (hKT : K ≤ T)
        (F : ChartCutoffFamily G K) (Q : ChartCutoffFamily G T)
        (p : Fin Q.count) (j : ℕ) (y : EuclideanSpace ℝ (Fin n)),
        y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) G.scaleRadius →
        ‖iteratedFDeriv ℝ j
          (selectorSourceAmbient (fun _ : Fin n ↦ G.palette)
            (actualColoredSource G g f F Q (hK.trans hKT) p)) y‖ ≤ B j ∧
        ‖iteratedFDeriv ℝ j
          (selectorSourceAmbientError (fun _ : Fin n ↦ G.palette)
            (actualColoredSource G g f F Q (hK.trans hKT) p)
            (coframeRows (actualReferenceCoframe G g f (Q.parent p) (Q.center p) T))) y‖ ≤
              A j * (K⁻¹ + K / T) := by
  obtain ⟨cutoffB, hcutoffB, hcutoff⟩ := exists_actual_cutoff_wave_budgets G
  obtain ⟨L, hL, hphase⟩ := exists_actual_scalarPhase_reference_budgets G g f
  obtain ⟨R, hR, hrate⟩ := exists_actual_scalarRate_error_budgets G g f
  let a : ℕ → ℝ := fun j ↦ cutoffB j + R j
  have ha (j : ℕ) : 0 ≤ a j := by dsimp [a]; linarith [hcutoffB j, hR j]
  have hDa (j : ℕ) : cutoffB j ≤ a j := by dsimp [a]; linarith [hR j]
  have hRa (j : ℕ) : R j ≤ a j := by dsimp [a]; linarith [hcutoffB j]
  let B : ℕ → ℝ := fun j ↦ ((G.palette : ℝ) + 1) * coloredWaveReferenceBound (a j) (L j) j
  let A : ℕ → ℝ := fun j ↦ ((G.palette : ℝ) + 1) * coloredWaveErrorBound (a j) (L j) j
  refine ⟨B, A, ?_, ?_, ?_⟩
  · intro j
    exact mul_nonneg (by positivity) (coloredWaveReferenceBound_nonneg _ _ (ha j) j)
  · intro j
    exact mul_nonneg (by positivity) (coloredWaveErrorBound_nonneg _ _ (ha j) j)
  · intro K T hK hKT F Q p j y hy
    let φ := ((Q.boundedAtlas (hK.trans hKT)).chart p).symm
    let c := actualReferenceCoframe G g f (Q.parent p) (Q.center p) T
    let r := coframeRows c
    have hφ : ContinuousAt φ y := ((Q.boundedAtlas (hK.trans hKT)).chart p).symm.continuousAt hy
    have hZ := actualColoredSource_ambient_contDiffOn G g f F Q (hK.trans hKT) p
    have hc : ContDiffOn ℝ ∞ c (ball (0 : EuclideanSpace ℝ (Fin n)) G.scaleRadius) :=
      actualReferenceCoframe_contDiffOn_ball G g f Q (hK.trans hKT) p
    have hr (l : Fin n) : ContDiffOn ℝ ∞ (fun z ↦ r z l)
        (ball (0 : EuclideanSpace ℝ (Fin n)) G.scaleRadius) :=
      coframeRows_contDiffOn c _ hc l
    have hδ : 0 ≤ K⁻¹ + K / T := (initialization_error_scale_bounds hK hKT).2.2.1
    have hterms (l : Fin n) (i : Fin F.count) (hi : φ y ∈ tsupport (F.cutoff i)) :
        ‖iteratedFDeriv ℝ j
          (coloredWave (F.cutoff i ∘ φ)
            (preparedFrozenPhase F (preparedCoframe G g f) l i ∘ φ) T) y‖ ≤
              coloredWaveReferenceBound (a j) (L j) j ∧
        ‖iteratedFDeriv ℝ j
          (coloredWaveFirstRemainder (F.cutoff i ∘ φ)
            (preparedFrozenPhase F (preparedCoframe G g f) l i ∘ φ) T (fun z ↦ r z l)) y‖ ≤
              coloredWaveErrorBound (a j) (L j) j * (K⁻¹ + K / T) := by
      obtain ⟨O, hO, hyO, hsub, hχO, hℓO⟩ :=
        exists_actual_phase_smooth_neighborhood G g f F Q (hK.trans hKT) p i l y hy hi
      have hχ := hcutoff K T hK hKT F Q p i j y hy
      have hχlarge (k : ℕ) (hk : k ≤ j) :
          ‖iteratedFDeriv ℝ k (F.cutoff i ∘ φ) y‖ ≤ a j := (hχ.1 k hk).trans (hDa j)
      have hχsmall (k : ℕ) (hk : k ≤ j) :
          ‖iteratedFDeriv ℝ (k+1) (F.cutoff i ∘ φ) y‖ ≤ a j * (K⁻¹ + K / T) :=
        (hχ.2 k hk).trans (mul_le_mul_of_nonneg_right (hDa j) hδ)
      have hrate' (k : ℕ) (hk : k ≤ j) :
          ‖iteratedFDeriv ℝ k (fun z ↦
            T • fderiv ℝ (preparedFrozenPhase F (preparedCoframe G g f) l i ∘ φ) z - r z l) y‖ ≤
              a j * (K⁻¹ + K / T) :=
        (hrate K T hK hKT F Q p i l j y hy hi k hk).trans
          (mul_le_mul_of_nonneg_right (hRa j) hδ)
      have hp := hphase K T hK hKT F Q p i l j y hy hi
      constructor
      · exact coloredWave_reference_bound O hO _ _ hχO hℓO T (a j) (L j) (ha j) y hyO j hχlarge hp
      · exact coloredWaveFirstRemainder_jet_bound O hO _ _ _ hχO hℓO ((hr l).mono hsub)
          T (a j) (L j) (K⁻¹ + K/T) (ha j) hδ y hyO j hχlarge hχsmall hp hrate'
    constructor
    · exact coloredProduct_pullback_reference_jet_bound F.color F.cutoff
        (preparedFrozenPhase F (preparedCoframe G g f)) F.same_color_disjoint T φ y hφ
        (hZ.contDiffAt (isOpen_ball.mem_nhds hy)) j
        (coloredWaveReferenceBound (a j) (L j) j)
        (coloredWaveReferenceBound_nonneg _ _ (ha j) j) (fun l i hi ↦ (hterms l i hi).1)
    · have hb := coloredSourceAmbientError_jet_bound F.color F.cutoff
        (preparedFrozenPhase F (preparedCoframe G g f)) F.same_color_disjoint F.sum_sq T φ r
        (ball (0 : EuclideanSpace ℝ (Fin n)) G.scaleRadius) isOpen_ball hZ hr
        y hy hφ j (coloredWaveErrorBound (a j) (L j) j * (K⁻¹ + K/T))
        (mul_nonneg (coloredWaveErrorBound_nonneg _ _ (ha j) j) hδ)
        (fun l i hi ↦ (hterms l i hi).2)
      exact hb.trans_eq (by dsimp [A]; ring)

end GlobalEmbedding.Initialization
