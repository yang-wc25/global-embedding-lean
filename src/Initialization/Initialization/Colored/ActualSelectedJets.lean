import Initialization.Colored.ActualColoredJets

/-!
# Actual selected-map reference and error jets

The native sphere argument already has internally produced all-order bounds.
The same compact selector supplies the outer derivative constants, and the
proved chain-rule remainder identity supplies the actual selected-map error.
Both output sequences are chosen before K,T and any scale-dependent net.
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
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def actualSelectedCoordinate
    (S : FreeHopfProduct (fun _ : Fin n ↦ G.palette) → V)
    {K T : ℝ} (F : ChartCutoffFamily G K) (Q : ChartCutoffFamily G T)
    (hT : 1 ≤ T) (p : Fin Q.count) : EuclideanSpace ℝ (Fin n) → V :=
  S ∘ actualColoredSource G g f F Q hT p

theorem metricInitializationMap_pullback_eq_actualSelectedCoordinate
    (S : FreeHopfProduct (fun _ : Fin n ↦ G.palette) → V)
    {K T : ℝ} (hK : 1 ≤ K) (Q : ChartCutoffFamily G T) (hT : 1 ≤ T) (p : Fin Q.count) :
    metricInitializationMap G g f S K T hK ∘ ((Q.boundedAtlas hT).chart p).symm =
      actualSelectedCoordinate G g f S (preparedCutoffsAt G K hK) Q hT p := rfl

/-- Actual all-order H reference bounds, actual first-error jet bounds, and the
actual finite C^j error norm. There are no geometric or analytic budget inputs. -/
theorem exists_actualSelectedSource_jet_bounds
    (S : FreeHopfProduct (fun _ : Fin n ↦ G.palette) → V)
    (hS : ContMDiff (freeHopfModel (fun _ : Fin n ↦ G.palette)) 𝓘(ℝ, V) ∞ S) :
    ∃ (R A : ℕ → ℝ), (∀ j, 0 < R j) ∧ (∀ j, 0 < A j) ∧
      ∀ (K T : ℝ) (hK : 1 ≤ K) (hKT : K ≤ T)
        (F : ChartCutoffFamily G K) (Q : ChartCutoffFamily G T)
        (p : Fin Q.count) (j : ℕ),
        (∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) G.scaleRadius,
          ‖iteratedFDeriv ℝ j (actualSelectedCoordinate G g f S F Q (hK.trans hKT) p) y‖ ≤ R j ∧
          ‖iteratedFDeriv ℝ j
            (selectorSourceFirstError (fun _ : Fin n ↦ G.palette) S
              (actualColoredSource G g f F Q (hK.trans hKT) p)
              (coframeRows (actualReferenceCoframe G g f (Q.parent p) (Q.center p) T))) y‖ ≤
                A j * (K⁻¹ + K / T)) ∧
        finiteCjNorm j
          (selectorSourceFirstError (fun _ : Fin n ↦ G.palette) S
            (actualColoredSource G g f F Q (hK.trans hKT) p)
            (coframeRows (actualReferenceCoframe G g f (Q.parent p) (Q.center p) T)))
          (ball (0 : EuclideanSpace ℝ (Fin n)) G.scaleRadius) ≤ A j * (K⁻¹ + K / T) := by
  obtain ⟨ZB, EB, hZB, hEB, hraw⟩ := exists_actualColoredSource_jet_bounds G g f
  let U : ℕ → ℝ := fun j ↦ 1 + coloredSelectorOuterEnvelope ZB j
  have hZU {k j : ℕ} (hkj : k ≤ j) : ZB k ≤ U j := by
    have h := le_coloredSelectorOuterEnvelope ZB hZB hkj
    dsimp [U]
    linarith
  obtain ⟨R, hR, href⟩ := exists_selectorSource_reference_bounds
    (E := EuclideanSpace ℝ (Fin n)) (fun _ : Fin n ↦ G.palette) S hS U
  let a : ℕ → ℝ := fun j ↦ 1 + coloredSelectorOuterEnvelope R j
  let b : ℕ → ℝ := fun j ↦ 1 + coloredSelectorOuterEnvelope EB j
  have ha (j : ℕ) : 0 ≤ a j := by
    dsimp [a]
    linarith [coloredSelectorOuterEnvelope_nonneg R (fun k ↦ (hR k).le) j]
  have hb (j : ℕ) : 0 ≤ b j := by
    dsimp [b]
    linarith [coloredSelectorOuterEnvelope_nonneg EB hEB j]
  have hRa {k j : ℕ} (hkj : k ≤ j) : R k ≤ a j := by
    have h := le_coloredSelectorOuterEnvelope R (fun k ↦ (hR k).le) hkj
    dsimp [a]
    linarith
  have hEb {k j : ℕ} (hkj : k ≤ j) : EB k ≤ b j := by
    have h := le_coloredSelectorOuterEnvelope EB hEB hkj
    dsimp [b]
    linarith
  let A : ℕ → ℝ := fun j ↦ max 1
    ((∑ k ∈ Finset.range (j+1), (2 : ℝ)^k) * a j * b j)
  refine ⟨R, A, hR, fun _ ↦ lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro K T hK hKT F Q p j
  let z := actualColoredSource G g f F Q (hK.trans hKT) p
  let c := actualReferenceCoframe G g f (Q.parent p) (Q.center p) T
  let r := coframeRows c
  let O := ball (0 : EuclideanSpace ℝ (Fin n)) G.scaleRadius
  have hZ := actualColoredSource_ambient_contDiffOn G g f F Q (hK.trans hKT) p
  have hc := actualReferenceCoframe_contDiffOn_ball G g f Q (hK.trans hKT) p
  have hr (l : Fin n) : ContDiffOn ℝ ∞ (fun y ↦ r y l) O := coframeRows_contDiffOn c O hc l
  have hδ : 0 ≤ K⁻¹ + K / T := (initialization_error_scale_bounds hK hKT).2.2.1
  have hre (k : ℕ) (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ O) :
      ‖iteratedFDeriv ℝ k (S ∘ z) y‖ ≤ R k ∧
      ‖iteratedFDeriv ℝ k (selectorSourceOuterDerivative (fun _ : Fin n ↦ G.palette) S z) y‖ ≤ R k := by
    apply href z O isOpen_ball hZ y hy k
    intro i _ hik
    exact ((hraw K T hK hKT F Q p i y hy).1).trans (hZU hik)
  have houter (k : ℕ) (hk : k ≤ j) (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ O) :
      ‖iteratedFDeriv ℝ k (selectorSourceOuterDerivative (fun _ : Fin n ↦ G.palette) S z) y‖ ≤ a j :=
    (hre k y hy).2.trans (hRa hk)
  have herr (k : ℕ) (hk : k ≤ j) (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ O) :
      ‖iteratedFDeriv ℝ k (selectorSourceAmbientError (fun _ : Fin n ↦ G.palette) z r) y‖ ≤
        b j * (K⁻¹ + K / T) :=
    ((hraw K T hK hKT F Q p k y hy).2).trans (mul_le_mul_of_nonneg_right (hEb hk) hδ)
  have he := selectorSourceFirstError_cj_bound S hS z r j O isOpen_ball hZ hr
    (a j) (b j) (K⁻¹ + K/T) (ha j) (hb j) hδ houter herr
  have hcoef : (2 : ℝ)^j * a j * b j ≤ A j := by
    have hp : (2 : ℝ)^j ≤ ∑ k ∈ Finset.range (j+1), (2 : ℝ)^k :=
      Finset.single_le_sum (fun _ _ ↦ by positivity) (by simp)
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp (ha j)) (hb j)).trans
      (le_max_right _ _)
  constructor
  · intro y hy
    exact ⟨(hre j y hy).1, (he.1 j le_rfl y hy).trans (mul_le_mul_of_nonneg_right hcoef hδ)⟩
  · exact he.2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hδ)

end GlobalEmbedding.Initialization
