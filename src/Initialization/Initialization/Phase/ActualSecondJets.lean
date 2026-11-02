import Initialization.Phase.SelectorSecondBounds
import Initialization.Colored.ActualSelectedJets
import Initialization.Geometry.BoundedCoframeGeometry

/-!
# Actual initialization first and second jet budgets

Every constant in this file is produced from the original metric, actual finite
chart preparation and one fixed smooth native selector. The sphere argument,
coframe field, first derivative and second derivative are the literal ones of
the same colored initialization map. No jet or geometry budget is an input.
The second error uses the original canonical symmetric-square quotient norm.
-/

noncomputable section
open Set Function Metric Manifold Bundle GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff TensorProduct

namespace GlobalEmbedding.Initialization

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance actualSecondRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance actualSecondSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {n N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M] [CompactSpace M]

variable (G : PreparedCharts M n)
  (g : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
    (EuclideanSpace ℝ (Fin n))
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _))
  (f : FullTangentFrame 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M := M) n)
  (S : FreeHopfProduct (fun _ : Fin n ↦ G.palette) → EuclideanSpace ℝ (Fin N))

private theorem actualCoframeRows_eq
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)) : selectorCoframeRates c = coframeRows c := by
  funext x i
  apply ContinuousLinearMap.ext
  intro v
  rfl

/-- The same fixed data supplies both actual jet errors for every real scale,
all net choices and every point of the entire scale-chart target. -/
theorem exists_actualSelected_twoJet_error_bounds
    (hS : ContMDiff (freeHopfModel (fun _ : Fin n ↦ G.palette))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ S) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (K T : ℝ) (hK : 1 ≤ K) (hKT : K ≤ T)
        (F : ChartCutoffFamily G K) (Q : ChartCutoffFamily G T)
        (p : Fin Q.count) (y : EuclideanSpace ℝ (Fin n)),
        y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) G.scaleRadius →
        let z := actualColoredSource G g f F Q (hK.trans hKT) p
        let c := actualReferenceCoframe G g f (Q.parent p) (Q.center p) T
        ‖(selectorIdealFirstJet (fun _ : Fin n ↦ G.palette) S (z y)).comp (c y) -
          fderiv ℝ (S ∘ z) y‖ ≤ A * (K⁻¹ + K / T) ∧
        ‖coordinateHessianJet (S ∘ z) y -
          ((selectorIdealSecondJet (fun _ : Fin n ↦ G.palette) S (z y)).comp
            (symmetricSquareMapL (c y)) +
            (selectorIdealFirstJet (fun _ : Fin n ↦ G.palette) S (z y)).comp
              (actualHessianLift (fderiv ℝ c y)))‖ ≤ A * (K⁻¹ + K / T) := by
  obtain ⟨CB, L, hCB, _hL, hcoframe⟩ := exists_boundedAtlas_coframe_geometry G g f
  obtain ⟨ZB, ZE, _hZB, hZE, hraw⟩ := exists_actualColoredSource_jet_bounds G g f
  obtain ⟨HB, HE, _hHB, hHE, hselected⟩ := exists_actualSelectedSource_jet_bounds G g f S hS
  obtain ⟨YB, hYB, hcolumn⟩ := selectorHopfExtension_uniform_first_bound
    (fun _ : Fin n ↦ G.palette) S hS
  let liftC := actualHessianLiftConstant (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin N))
  have hlift : 0 ≤ liftC := actualHessianLiftConstant_nonneg
  let secondC : ℝ := liftC * ((n : ℝ) * CB 0 * YB * ZE 0 + HE 1)
  have hsecondC : 0 ≤ secondC := by
    dsimp [secondC]
    positivity [hCB 0, hZE 0, hHE 1]
  let A : ℝ := 1 + HE 0 + secondC
  have hA : 0 < A := by dsimp [A]; linarith [hHE 0]
  refine ⟨A, hA, ?_⟩
  intro K T hK hKT F Q p y hy
  let z := actualColoredSource G g f F Q (hK.trans hKT) p
  let c := actualReferenceCoframe G g f (Q.parent p) (Q.center p) T
  let δ : ℝ := K⁻¹ + K / T
  have hδ : 0 ≤ δ := (initialization_error_scale_bounds hK hKT).2.2.1
  have hgeo := hcoframe T (hK.trans hKT) Q p
  have hyt : y ∈ ((Q.boundedAtlas (hK.trans hKT)).chart p).target := hy
  have hcnorm : ‖c y‖ ≤ CB 0 := (hgeo.2 y hyt).1
  have hc : ContDiffAt ℝ ∞ c y :=
    hgeo.1.contDiffAt (((Q.boundedAtlas (hK.trans hKT)).chart p).open_target.mem_nhds hyt)
  have hz : ContDiffAt ℝ ∞ (selectorSourceAmbient (fun _ : Fin n ↦ G.palette) z) y :=
    (actualColoredSource_ambient_contDiffOn G g f F Q (hK.trans hKT) p).contDiffAt
      (isOpen_ball.mem_nhds hy)
  have hEZ : ‖selectorSourceAmbientError (fun _ : Fin n ↦ G.palette) z (selectorCoframeRates c) y‖ ≤
      ZE 0 * δ := by
    simpa only [actualCoframeRows_eq, norm_iteratedFDeriv_zero] using (hraw K T hK hKT F Q p 0 y hy).2
  have hEH : ‖selectorSourceFirstError (fun _ : Fin n ↦ G.palette) S z (coframeRows c) y‖ ≤
      HE 0 * δ := by
    simpa only [norm_iteratedFDeriv_zero] using ((hselected K T hK hKT F Q p 0).1 y hy).2
  have hDEH : ‖fderiv ℝ (selectorSourceFirstError (fun _ : Fin n ↦ G.palette) S z
      (selectorCoframeRates c)) y‖ ≤ HE 1 * δ := by
    simpa only [actualCoframeRows_eq, norm_iteratedFDeriv_one] using ((hselected K T hK hKT F Q p 1).1 y hy).2
  constructor
  · have heq : (selectorIdealFirstJet (fun _ : Fin n ↦ G.palette) S (z y)).comp (c y) =
        selectorSourceIdealFirst (fun _ : Fin n ↦ G.palette) S z (coframeRows c) y :=
      (selectorSourceIdealFirst_eq_gramFrame S z c y).symm
    rw [heq, norm_sub_rev]
    exact hEH.trans (mul_le_mul_of_nonneg_right (by dsimp [A]; linarith) hδ)
  · have hb := coordinateHessianJet_selector_error_bound (fun _ : Fin n ↦ G.palette) S hS
      z c hz hc YB hYB.le (fun i ↦ hcolumn i (z y))
    apply hb.trans
    calc
      liftC * ((n : ℝ) * ‖c y‖ * YB *
          ‖selectorSourceAmbientError (fun _ : Fin n ↦ G.palette) z (selectorCoframeRates c) y‖ +
          ‖fderiv ℝ (selectorSourceFirstError (fun _ : Fin n ↦ G.palette) S z
            (selectorCoframeRates c)) y‖) ≤
          liftC * ((n : ℝ) * CB 0 * YB * (ZE 0 * δ) + HE 1 * δ) := by
        apply mul_le_mul_of_nonneg_left _ hlift
        apply add_le_add _ hDEH
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcnorm (by positivity)) hYB.le)
          hEZ (norm_nonneg _) (by positivity [hCB 0])
      _ = secondC * δ := by dsimp [secondC]; ring
      _ ≤ A * δ := mul_le_mul_of_nonneg_right (by dsimp [A]; linarith [hHE 0]) hδ

end GlobalEmbedding.Initialization
