import Initialization.Phase.ActualSecondJets
import Initialization.Phase.ChartPhase
import Initialization.Assembly.ParameterThresholds

/-!
# Uniform positive phase margin of the actual initialization map

The fixed selector, genuine metric-normalized coframe, actual cutoffs and actual
scaled charts now supply every hypothesis of pointwise phase stability. Both
large-parameter thresholds and the strictly positive retained margin are fixed
before K,T. The source may be disconnected or empty. Only n≥2 is used for the
original nontrivial hyperplane phase criterion.
-/

noncomputable section
open Set Function Metric Manifold Bundle GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff TensorProduct

namespace GlobalEmbedding.Initialization

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance actualMarginRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance actualMarginSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

private theorem actualHessianLift_norm_bound
    {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (B : E →L[ℝ] E →L[ℝ] V) :
    ‖actualHessianLift B‖ ≤ actualHessianLiftConstant E V * ‖B‖ := by
  have h := actualHessianLift_sub_norm_le B (0 : E →L[ℝ] E →L[ℝ] V)
  have hz : actualHessianLift (0 : E →L[ℝ] E →L[ℝ] V) = 0 :=
    (actualHessianLift (E := E) (F := V)).map_zero
  rw [hz, sub_zero, sub_zero] at h
  exact h

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞ M] [T2Space M] [CompactSpace M]

variable (G : PreparedCharts M (m+1))
  (g : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞
    (EuclideanSpace ℝ (Fin (m+1)))
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) : M → Type _))
  (f : FullTangentFrame 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) (M := M) (m+1))

/-- The same actual colored selected map is uniformly immersive and has a
strictly positive original phase functional in every chosen rescaled chart.
All geometric, coframe, selector and error reserves are produced internally.
The remaining data G, f and P have their own existence producers from precisely
the original compactness and parallelizability assumptions. -/
theorem exists_actual_initialization_phase_margin (hm : 1 ≤ m)
    (P : SelectorPhaseReference (fun _ : Fin (m+1) ↦ G.palette)) :
    ∃ η K₀ R₀ : ℝ, 0 < η ∧ 1 ≤ K₀ ∧ 1 ≤ R₀ ∧
      ∀ (K T : ℝ) (hK : 1 ≤ K) (hKT : K ≤ T),
        K₀ ≤ K → R₀ * K ≤ T →
        ∀ (F : ChartCutoffFamily G K) (Q : ChartCutoffFamily G T)
          (p : Fin Q.count) (y : EuclideanSpace ℝ (Fin (m+1))),
          y ∈ ((Q.boundedAtlas (hK.trans hKT)).chart p).target →
          Function.Injective
            (fderiv ℝ (actualSelectedCoordinate G g f P.selector F Q (hK.trans hKT) p) y) ∧
          η ≤ chartPhaseMargin
            (actualSelectedCoordinate G g f P.selector F Q (hK.trans hKT) p) y := by
  obtain ⟨B, L, hB, hL, hgeometry⟩ := exists_boundedAtlas_coframe_geometry G g f
  obtain ⟨A, hA, herror⟩ := exists_actualSelected_twoJet_error_bounds G g f P.selector P.smooth
  let liftC := actualHessianLiftConstant (EuclideanSpace ℝ (Fin (m+1)))
    (EuclideanSpace ℝ (Fin (m+1)))
  let Rbound := liftC * B 1
  have hdim : 2 ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+1))) := by
    simpa using (Nat.succ_le_succ hm)
  obtain ⟨δ, hδ, hstable⟩ := selector_chart_phase_stability hdim P
    (B 0) L Rbound (zero_le_one.trans (hB 0)) (zero_le_one.trans hL)
  obtain ⟨K₀, R₀, hK₀, hR₀, hsmall⟩ := initialization_error_scale_eventually_small A δ hA.le hδ
  refine ⟨P.retainedMargin L, K₀, R₀, P.retainedMargin_pos L, hK₀, hR₀, ?_⟩
  intro K T hK hKT hKK hTT F Q p y hy
  let z := actualColoredSource G g f F Q (hK.trans hKT) p
  let c := actualReferenceCoframe G g f (Q.parent p) (Q.center p) T
  let e := boundedAtlasCoframeEquiv G g f Q (hK.trans hKT) p y hy
  have hg := hgeometry T (hK.trans hKT) Q p
  have hgy := hg.2 y hy
  have heq : e.toContinuousLinearMap = c y := rfl
  have hz : ContDiffAt ℝ ∞ (selectorSourceAmbient (fun _ : Fin (m+1) ↦ G.palette) z) y :=
    (actualColoredSource_ambient_contDiffOn G g f F Q (hK.trans hKT) p).contDiffAt
      (isOpen_ball.mem_nhds hy)
  have hDc : ‖fderiv ℝ c y‖ ≤ B 1 := by
    simpa only [norm_iteratedFDeriv_one] using hgy.2.2.2.1 1
  have hcorrection : ‖actualHessianLift (fderiv ℝ c y)‖ ≤ Rbound :=
    (actualHessianLift_norm_bound (fderiv ℝ c y)).trans
      (mul_le_mul_of_nonneg_left hDc actualHessianLiftConstant_nonneg)
  have hsmall' : A * (K⁻¹ + K / T) < δ := (hsmall K T hKK hTT).2.2.2
  have herr := herror K T hK hKT F Q p y hy
  have hs := hstable z c y e heq hz hgy.1 hgy.2.1 hcorrection
    (herr.1.trans hsmall'.le) (herr.2.trans hsmall'.le)
  exact ⟨hs.1, hs.2.1⟩

/-- The literal global map (7.2), pulled back by the actual scaled chart,
therefore has the same internally produced margin. This is the direct consumer
for the full initialization proposition and global immersion transfer. -/
theorem exists_metricInitializationMap_phase_margin (hm : 1 ≤ m)
    (P : SelectorPhaseReference (fun _ : Fin (m+1) ↦ G.palette)) :
    ∃ η K₀ R₀ : ℝ, 0 < η ∧ 1 ≤ K₀ ∧ 1 ≤ R₀ ∧
      ∀ (K T : ℝ) (hK : 1 ≤ K) (hKT : K ≤ T),
        K₀ ≤ K → R₀ * K ≤ T →
        ∀ (Q : ChartCutoffFamily G T) (p : Fin Q.count)
          (y : EuclideanSpace ℝ (Fin (m+1))),
          y ∈ ((Q.boundedAtlas (hK.trans hKT)).chart p).target →
          Function.Injective (fderiv ℝ
            (metricInitializationMap G g f P.selector K T hK ∘
              ((Q.boundedAtlas (hK.trans hKT)).chart p).symm) y) ∧
          η ≤ chartPhaseMargin
            (metricInitializationMap G g f P.selector K T hK ∘
              ((Q.boundedAtlas (hK.trans hKT)).chart p).symm) y := by
  obtain ⟨η, K₀, R₀, hη, hK₀, hR₀, hphase⟩ :=
    exists_actual_initialization_phase_margin G g f hm P
  exact ⟨η, K₀, R₀, hη, hK₀, hR₀,
    fun K T hK hKT hKK hTT Q p y hy ↦
      hphase K T hK hKT hKK hTT (preparedCutoffsAt G K hK) Q p y hy⟩

end GlobalEmbedding.Initialization
