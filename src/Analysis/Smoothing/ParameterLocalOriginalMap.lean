import Smoothing.ParameterLocalOriginalMapNorms
import GlobalEmbedding.Offline.FixedSmoothingKernel
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Original total-joint (6.4) for the actual map with only local parameter charts

The finite parameter chart family has no global cover field. On the open W
of its square partition, the SAME actual Euclidean map has the literal
original total C^(j+2) tail. Source bounds are evaluated on the true fixed
independent source/parameter sampling buffers, whose parameter-set component
is univ. A budget restricted to K is not automatically a sampling budget.
Original local coordinate smoothness, rather than global smoothness of the
input outside the chart family, suffices.
-/

open GlobalEmbedding.Offline GlobalEmbedding.Paper Function Set MeasureTheory Manifold IsManifold
open scoped ContDiff Topology ENNReal BigOperators
namespace GlobalEmbedding.Continuation
noncomputable section

variable {n d q pcount : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]

local instance parameterLocalOriginalMapChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance parameterLocalOriginalMapIsManifold : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) P M

local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ey" => EuclideanSpace ℝ (Fin q)
local notation "cp" => EuclideanSpace.equiv (Fin d) ℝ
local notation "cs" => EuclideanSpace.equiv (Fin n) ℝ
local notation "cy" => EuclideanSpace.equiv (Fin q) ℝ

theorem fixedKernel_original_local_parameter_total_map_smoothing_tail
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ, Ep) ∞ P)
    (rho : ℝ) (hrho : 0 < rho) (hbuffer : rho ≤ min B.buffer A.buffer) (m r : ℕ)
    {tau ell t : ℝ} (htau : 0 < tau) (htaul : tau ≤ ell) (helt : ell ≤ t) (ht1 : t ≤ 1)
    (chi : (Fin A.count × Fin pcount) → P × M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ (parameterLocalProductFamily A B).inner i)
    (W : Set P) (hW : IsOpen W)
    (hpartition : ∀ z : P × M, z.1 ∈ W → ∑ i, chi i z ^ 2 = 1)
    {u : P × M → Ey} (hu : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B.chart u i)
      (incrementsOriginalDifferentiation A B.chart i))
    (Bc T : ℕ → ℝ) (hBc : ∀ j, 0 ≤ Bc j) (hT : ∀ j, 0 ≤ T j) (D : ℕ)
    (hD : ∀ z, (activeCutoffIndices chi z).card ≤ D)
    (hweight : ∀ p i k, ∀ y ∈ tensorLocalInner (parameterLocalProductFamily A B) p,
      ((parameterLocalProductFamily A B).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (chi i ∘ ((parameterLocalProductFamily A B).chart p).symm) y‖ ≤ Bc k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ tensorLocalInner (parameterLocalProductFamily A B) p,
      ((parameterLocalProductFamily A B).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k ((parameterLocalProductFamily A B).chart i ∘ ((parameterLocalProductFamily A B).chart p).symm) y‖ ≤ T k)
    (hNr : paperAtlasWeighted 2 r t (incrementsOriginalMapCoordinates A B.chart u)
      (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalSampling A B) ≠ ⊤)
    (hNm : paperAtlasWeighted 2 m t (incrementsOriginalMapCoordinates A B.chart u)
      (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalSampling A B) ≠ ⊤)
    (budget : ℝ) (hbudget : (paperAtlasWeighted 2 r t
      (incrementsOriginalMapCoordinates A B.chart u) (incrementsOriginalDifferentiation A B.chart)
      (tensorLocalOriginalSampling A B)).toReal ≤ budget) :
    let mu := (volume : Measure (Ep × Es))
    let K := fixedSmoothingKernel mu rho hrho r
    let kappa := normalizedSmoothingBase mu rho hrho
    let S := parameterLocalMapSmoothing (parameterLocalProductFamily A B) mu K ell chi u
    let O := incrementsOriginalDifferentiation A B.chart
    let e := incrementsOriginalMapCoordinates A B.chart (fun z => u z - S z)
    ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ S ∧
    paperAtlasWeighted 2 m tau e O (tensorLocalOriginalInner A B W) ≠ ⊤ ∧
    (paperAtlasWeighted 2 m tau e O (tensorLocalOriginalInner A B W)).toReal ≤
      modelBufferedSmoothingTailConstant (parameterTensorModelEquiv n d) mu kappa Bc T D 2 m r *
        (budget * (ell / t) ^ r + (paperAtlasWeighted 2 m t
          (incrementsOriginalMapCoordinates A B.chart u) O
          (tensorLocalOriginalSampling A B)).toReal * (tau / t) ^ r) := by
  dsimp only
  let C := parameterLocalProductFamily A B
  let mu := (volume : Measure (Ep × Es))
  let K := fixedSmoothingKernel mu rho hrho r
  let S := parameterLocalMapSmoothing C mu K ell chi u
  let c := parameterTensorModelEquiv n d
  have hC := parameterLocalProductFamily_chart_mem A B hA hB
  haveI : mu.IsAddHaarMeasure := by
    dsimp only [mu]
    rw [Measure.volume_eq_prod]
    infer_instance
  have hb := normalizedSmoothingBase_spec mu rho hrho
  have hK := fixedSmoothingKernel_spec mu rho hrho r
  have huPi := parameterLocalMapInputPi_contDiffOn A B u hu
  have huNative := parameterLocalMapInput_contDiffOn A B u hu
  have hS := parameterLocalMapSmoothing_contMDiff C hC mu hK.1 hK.2.1 hK.2.2.1
    hbuffer (htau.trans_le htaul).le (helt.trans ht1) chi hchi hchiSupport u huNative
  have hSorig : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B.chart S i)
      (incrementsOriginalDifferentiation A B.chart i) := by
    have hSPi : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Fin q → ℝ) ∞ (cy ∘ S) :=
      (cy).contDiff.contMDiff.comp hS
    have hSnative : ∀ j, ContDiffOn ℝ ∞ ((cy ∘ S) ∘ (C.chart j).symm) (C.chart j).target := by
      intro j
      letI : ChartedSpace (Ep × Es) (Ep × Es) := chartedSpaceSelf (Ep × Es)
      have hj : ContMDiffOn 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ep × Es) ∞ (C.chart j).symm (C.chart j).target :=
        contMDiffOn_symm_of_mem_maximalAtlas (hC j)
      have hcomp : ContMDiffOn 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Fin q → ℝ) ∞
          ((cy ∘ S) ∘ (C.chart j).symm) (C.chart j).target := hSPi.comp_contMDiffOn hj
      exact hcomp.contDiffOn
    intro i
    have hcoord := modelCoordinateFamily_contDiffOn c hSnative i
    change ContDiffOn ℝ ∞ (parameterLocalMapModelCoordinates C c (cy ∘ S) i)
      (tensorLocalModelTargets C c i) at hcoord
    rw [parameterLocalMapCoordinates_eq_original] at hcoord
    change ContDiffOn ℝ ∞ _ ((parameterTensorModelEquiv n d).symm ⁻¹' ((parameterLocalProductFamily A B).chart i).target) at hcoord
    rw [parameterLocalProduct_targets A B i] at hcoord
    exact hcoord
  have hNrLe := parameterLocalMap_weighted_sampling_le_original A B u 2 r t
  have hNmLe := parameterLocalMap_weighted_sampling_le_original A B u 2 m t
  have hNrN := ne_top_of_le_ne_top hNr hNrLe
  have hNmN := ne_top_of_le_ne_top hNm hNmLe
  have hbudgetN := (ENNReal.toReal_mono hNr hNrLe).trans hbudget
  have h := paperAtlasWeighted_model_parameterLocalMap_smoothing_tail C c hC mu
    hb.1 hb.2.1 hb.2.2.1 2 m r hK.2.2.1 hbuffer htau htaul helt ht1 chi hchi
    hchiSupport (Prod.fst ⁻¹' W) (hW.preimage continuous_fst) hpartition huPi
    Bc T hBc hT D hD hweight htransition hNrN hNmN budget hbudgetN
  dsimp only at h
  have hnatural := parameterLocalMapSmoothing_equiv C mu K ell chi cy u
  have herror : parameterLocalMapModelCoordinates C c
      (parameterLocalMapSmoothing C mu K ell chi (cy ∘ u) - (cy ∘ u)) =
      parameterLocalMapModelCoordinates C c (cy ∘ (fun z => S z-u z)) := by
    rw [hnatural]
    funext i z
    exact ((cy).map_sub _ _).symm
  dsimp only [K,fixedSmoothingKernel] at herror
  rw [herror] at h
  have hEq := parameterLocalMap_weighted_inner_eq_original A B (fun z => S z-u z) W 2 m tau
  rw [hEq] at h
  have hO : ∀ i, IsOpen (incrementsOriginalDifferentiation A B.chart i) := by
    intro i
    rw [← parameterLocalProduct_targets A B i]
    exact tensorLocalModelTargets_open _ _ _
  have hcomm := paperAtlasWeighted_sub_comm 2 m tau
    (incrementsOriginalMapCoordinates A B.chart u) (incrementsOriginalMapCoordinates A B.chart S)
    (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalInner A B W) hO
    (tensorLocalOriginalInner_subset A B W) hu hSorig
  change paperAtlasWeighted 2 m tau
    (incrementsOriginalMapCoordinates A B.chart (fun z => u z-S z)) _ _ =
    paperAtlasWeighted 2 m tau
    (incrementsOriginalMapCoordinates A B.chart (fun z => S z-u z)) _ _ at hcomm
  rw [← hcomm] at h
  refine ⟨hS, h.1, h.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _
    (modelBufferedSmoothingTailConstant_nonneg c mu _ hBc hT D 2 m r)
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_right (ENNReal.toReal_mono hNm hNmLe)
    (pow_nonneg (div_nonneg htau.le ((htau.trans_le htaul).trans_le helt).le) _)

#print axioms fixedKernel_original_local_parameter_total_map_smoothing_tail
end
end GlobalEmbedding.Continuation
