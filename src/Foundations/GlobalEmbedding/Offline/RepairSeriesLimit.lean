import GlobalEmbedding.Offline.ActualPhaseStability
import GlobalEmbedding.Offline.RepairSequenceScales
import GlobalEmbedding.Offline.RepairDisplacementBudget
import Mathlib.Geometry.Manifold.Algebra.SMul

/-!
# The actual repair series: smooth limit, prescribed metric and retained phase

Source: `literature/parallelizable-stable-plus-one/main.tex`, `thm:repair`,
lines 772–778. This is a conditional limit theorem for an actual sequence of
increments satisfying the original stage bounds and actual defect identities.
It does not construct the one-step repair maps or their geometric estimates.

The first theorem below treats the base map itself as the geometric reference.
The manuscript's preliminary scaled base is a distinct map; its displacement
must also be budgeted before applying the final phase-stability theorem.
-/

open Manifold Bundle Set Filter GlobalEmbedding.Paper
open scoped TensorProduct ContDiff Topology ENNReal

namespace GlobalEmbedding.Offline

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n N : ℕ}

/-- The canonical Euclidean coordinate representative commutes with the SAME
actual pointwise series. This is the native continuous linear equivalence's
`map_tsum` theorem, not an identification with a separately selected limit. -/
theorem euclideanCoordinateRepresentative_tsum
    (a : E ≃L[ℝ] (Fin n → ℝ)) (u : ℕ → E → EuclideanSpace ℝ (Fin N)) :
    euclideanCoordinateRepresentative a (fun x ↦ ∑' j, u j x) =
      fun z ↦ ∑' j, euclideanCoordinateRepresentative a (u j) z := by
  funext z
  simp only [euclideanCoordinateRepresentative, Function.comp_apply]
  exact (EuclideanSpace.equiv (Fin N) ℝ).map_tsum

/-- The original stage bounds on an outer finite norm domain imply a strict
C² budget for the actual Euclidean-valued sum on the inner open buffer.
The coordinate transformation is applied to the actual sum, and its equality
with the coordinate series is proved above. -/
theorem paperCoordinateC2_tsum_on_inner_buffer
    (a : E ≃L[ℝ] (Fin n → ℝ)) (u : ℕ → E → EuclideanSpace ℝ (Fin N))
    (stage : ℕ → ℕ) {O S U : Set (Fin n → ℝ)}
    (hO : IsOpen O) (hSO : S ⊆ O) (hU : IsOpen U) (hUS : U ⊆ S)
    (hu : ∀ j, ContDiffOn ℝ ∞ (euclideanCoordinateRepresentative a (u j)) O)
    (hstage : Tendsto stage atTop atTop) (hmin : ∀ j, 4 ≤ stage j)
    {t C : ℝ} (ht : 0 < t) (htsmall : t ≤ (1 / 2 : ℝ) ^ (5 : ℕ)) (hC : 0 < C)
    (hbound : ∀ j, paperCoordinateCj (stage j / 2)
      (euclideanCoordinateRepresentative a (u j)) O S ≤ ENNReal.ofReal (C * iterationScale t j)) :
    ContDiffOn ℝ ∞ (euclideanCoordinateRepresentative a (fun x ↦ ∑' j, u j x)) U ∧
    paperCoordinateCj 2 (euclideanCoordinateRepresentative a (fun x ↦ ∑' j, u j x)) U U <
      ENNReal.ofReal C := by
  have ht1 : t < 1 := by norm_num at htsmall ⊢; linarith
  have hUbound (j : ℕ) : paperCoordinateCj (stage j / 2)
      (euclideanCoordinateRepresentative a (u j)) U U ≤ ENNReal.ofReal (C * iterationScale t j) :=
    (paperCoordinateCj_restrict_buffer _ hO hSO hU hUS (hu j)).trans (hbound j)
  rw [euclideanCoordinateRepresentative_tsum]
  exact ⟨(smooth_series_on_of_paper_stage_bound hU
      (fun j ↦ euclideanCoordinateRepresentative a (u j)) stage
      (fun j ↦ (hu j).mono (hUS.trans hSO)) hstage ht ht1 hC.le hUbound).1,
    paperCoordinateCj_tsum_lt_of_stage_bound 2 hU
      (fun j ↦ euclideanCoordinateRepresentative a (u j)) stage
      (fun j ↦ (hu j).mono (hUS.trans hSO)) hstage hmin ht htsmall hC hUbound⟩

/-- The source's actual scaled initialization and the actual Euclidean series
fit the original C² budget on an inner open buffer. Both summation and the
initial scalar are transported through the canonical target equivalence. -/
theorem repair_displacement_euclidean_on_inner_buffer
    (a : E ≃L[ℝ] (Fin n → ℝ)) (F0 : E → EuclideanSpace ℝ (Fin N))
    (u : ℕ → E → EuclideanSpace ℝ (Fin N)) (stage : ℕ → ℕ)
    {O S U : Set (Fin n → ℝ)}
    (hO : IsOpen O) (hSO : S ⊆ O) (hU : IsOpen U) (hUS : U ⊆ S)
    (hF0 : ContDiffOn ℝ ∞ (euclideanCoordinateRepresentative a F0) O)
    (hu : ∀ j, ContDiffOn ℝ ∞ (euclideanCoordinateRepresentative a (u j)) O)
    (hstage : Tendsto stage atTop atTop) (hmin : ∀ j, 4 ≤ stage j)
    {t ρ B : ℝ} (ht : 0 < t) (htsmall : t ≤ (1 / 2 : ℝ) ^ (5 : ℕ))
    (hρ : 0 < ρ) (hB : 0 ≤ B) (htbudget : t ≤ ρ / (32 * (B + 1)))
    (hreference : paperCoordinateCj 2 (euclideanCoordinateRepresentative a F0) O S ≤
      ENNReal.ofReal B)
    (hbound : ∀ j, paperCoordinateCj (stage j / 2)
      (euclideanCoordinateRepresentative a (u j)) O S ≤
        ENNReal.ofReal ((ρ / 8) * iterationScale t j)) :
    ContDiffOn ℝ ∞ (euclideanCoordinateRepresentative a
      (fun x ↦ Real.sqrt (1 - (t ^ (10 : ℕ)) ^ 2) • F0 x + ∑' j, u j x)) U ∧
    paperCoordinateCj 2 (euclideanCoordinateRepresentative a
      (fun x ↦ Real.sqrt (1 - (t ^ (10 : ℕ)) ^ 2) • F0 x + (∑' j, u j x) - F0 x)) U U ≤
        ENNReal.ofReal (5 * ρ / 32) := by
  have hreferenceU := (paperCoordinateCj_restrict_buffer 2 hO hSO hU hUS hF0).trans hreference
  have hboundU (j : ℕ) := (paperCoordinateCj_restrict_buffer (stage j / 2)
    hO hSO hU hUS (hu j)).trans (hbound j)
  have h := repair_displacement_paperCoordinateCj_le 2 hU
    (euclideanCoordinateRepresentative a F0)
    (fun j ↦ euclideanCoordinateRepresentative a (u j)) stage
    (hF0.mono (hUS.trans hSO)) (fun j ↦ (hu j).mono (hUS.trans hSO))
    hstage hmin ht htsmall hρ hB htbudget hreferenceU hboundU
  simpa only [euclideanCoordinateRepresentative, Function.comp_def, map_add,
    map_sub, map_smul, ContinuousLinearEquiv.map_tsum] using h

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance repairLimitSquareRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance repairLimitSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

section ReferenceBase

variable {E H M V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [RiemannianBundle (TangentSpace I : M → Type _)]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n N : ℕ}

/-- The actual reference-based repair series has one smooth phase-regular
limit with its prescribed original metric and a retained positive true margin.

The inputs are actual original-coordinate stage bounds, an actual normalized
metric-defect identity with the manuscript's `delta_j = t_j^(stage_j)`, and the
fixed reference reserves. Differential convergence, vanishing of the varying
defect scale, and the final C² budget are proved here from those inputs. The
limit is explicitly `F0 + tsum f` throughout.

This theorem begins at the reference map `F0`. Applying it to a separately
scaled initial map requires accounting for the initial displacement; that
manuscript-specific budget is not silently omitted or asserted here. -/
theorem repair_series_limit_with_reference_base
    (a : E ≃L[ℝ] (Fin n → ℝ))
    (hdim : 2 ≤ Module.finrank ℝ E) (lam bound m L R : ℝ)
    (hlam : 0 < lam) (hm : 0 < m) (hR : 0 ≤ R)
    (hcast : ∀ x : M, ‖(tangentSpaceCastModel I x).toContinuousLinearMap‖ ≤ R) :
    ∃ ε : ℝ, 0 < ε ∧
    ∀ (F0 : M → EuclideanSpace ℝ (Fin N))
      (_hF0 : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F0)
      (f : ℕ → M → EuclideanSpace ℝ (Fin N)) (stage : ℕ → ℕ)
      (t : ℝ) (g : ∀ x : M, LinearMap.BilinForm ℝ (TangentSpace I x))
      (Hseq : ℕ → ∀ x : M, LinearMap.BilinForm ℝ (TangentSpace I x))
      (ξ : ∀ x : M, TangentSpace I x →L[ℝ] ℝ)
      (e : ∀ x : M, (ξ x).ker ≃L[ℝ] V)
      (S : M → SymmetricSquare V →L[ℝ] EuclideanSpace ℝ (Fin N)),
      Tendsto stage atTop atTop → (∀ j, 10 ≤ stage j) →
      0 < t → t ≤ (1 / 2 : ℝ) ^ (5 : ℕ) →
      (∀ x : M, ∃ O T U : Set (Fin n → ℝ),
        IsOpen O ∧ T ⊆ O ∧ IsOpen U ∧ U ⊆ T ∧ a (extChartAt I x x) ∈ U ∧
        (∀ j, ContDiffOn ℝ ∞
          (euclideanCoordinateRepresentative a (f j ∘ (extChartAt I x).symm)) O) ∧
        (∀ j, paperCoordinateCj (stage j / 2)
          (euclideanCoordinateRepresentative a (f j ∘ (extChartAt I x).symm)) O T ≤
            ENNReal.ofReal (ε * iterationScale t j))) →
      (∀ (x : M) (v w : TangentSpace I x),
        ∃ C : ℝ, ∀ᶠ j in atTop, ‖Hseq j x v w‖ ≤ C) →
      (∀ j x, g x - inducedMetric (I := I)
        (fun y ↦ F0 y + ∑ i ∈ Finset.range j, f i y) x =
          (iterationScale t j ^ stage j) ^ 2 • Hseq j x) →
      (∀ x v, lam * ‖v‖ ^ 2 ≤ ‖mvfderiv I F0 x v‖ ^ 2) →
      (∀ x, ‖actualCoordinateSecondJet (I := I) F0 x‖ ≤ bound) →
      (∀ x, ‖ξ x‖ = 1) → (∀ x, ‖(e x).symm.toContinuousLinearMap‖ ≤ L) →
      (∀ x, covectorRestriction
        (E := TangentSpace I x) (F := EuclideanSpace ℝ (Fin N))
        ((LinearMap.range (mvfderiv I F0 x).toLinearMap)ᗮ.starProjection.comp
          (actualCoordinateSecondJet (I := I) F0 x)) (ξ x) =
          (S x).comp (symmetricSquareMapL (e x).toContinuousLinearMap)) →
      (∀ x z, m * ‖z‖ ≤ ‖S x z‖) →
      (∀ x, Summable (fun j ↦ f j x)) ∧
      ∃ hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (fun x ↦ F0 x + ∑' j, f j x),
        inducedMetric (I := I) (fun x ↦ F0 x + ∑' j, f j x) = g ∧
        PhaseRegular (fun x ↦ F0 x + ∑' j, f j x) hF ∧
        ∀ x, (∀ v, (lam / 4) * ‖v‖ ^ 2 ≤ ‖mvfderiv I (fun y ↦ F0 y + ∑' j, f j y) x v‖ ^ 2) ∧
          m / (2 * (1 + L ^ 2)) ≤ truePhaseMargin (fun y ↦ F0 y + ∑' j, f j y) hF x := by
  obtain ⟨ε, hε, hphase⟩ := phase_regular_of_paperCoordinateC2_budget
    (I := I) (M := M) (V := V) (N := N) a hdim lam bound m L R hlam hm hR hcast
  refine ⟨ε, hε, ?_⟩
  intro F0 hF0 f stage t g Hseq ξ e S hstage hmin ht htsmall hchart hH hdefect
    hA hQ hξ hinv hselector hS
  have ht1 : t < 1 := by norm_num at htsmall ⊢; linarith
  have hmetric := smooth_repair_series_metric_limit_of_paper_stage_bounds a F0 f stage
    (fun j ↦ iterationScale t j ^ stage j) g Hseq hF0 hstage ht ht1
    (fun x ↦ by
      obtain ⟨O, T, U, hO, hTO, hU, hUT, hx, hf, hb⟩ := hchart x
      exact ⟨O, T, U, hO, hTO, hU, hUT, hx, hf, ε, hε.le, hb⟩)
    (tendsto_repair_defect_scale_zero ht ht1 stage hmin) hH hdefect
  have hp := hphase F0 (fun y ↦ F0 y + ∑' j, f j y) hF0 hmetric.2.1 ξ e S hA hQ
    (fun x ↦ by
      obtain ⟨O, T, U, hO, hTO, hU, hUT, hx, hf, hb⟩ := hchart x
      have hsum := paperCoordinateC2_tsum_on_inner_buffer a
        (fun j ↦ f j ∘ (extChartAt I x).symm) stage hO hTO hU hUT hf hstage
        (fun j ↦ by have := hmin j; omega) ht htsmall hε hb
      refine ⟨U, U, U, hU, Subset.rfl, hU, Subset.rfl, hx, ?_, ?_⟩
      · simpa only [Function.comp_def, add_sub_cancel_left] using hsum.1
      · simpa only [Function.comp_def, add_sub_cancel_left] using hsum.2.le)
    hξ hinv hselector hS
  exact ⟨hmetric.1, hmetric.2.1, hmetric.2.2, hp.1, hp.2⟩


/-- The source's scaled initialization, every actual increment, and the actual
normalized defect yield ONE smooth phase-regular isometric limit. The reference
map is `F0`, while the iterated base is `sqrt (1-t^20) • F0`. The initial
scaling is included in the proved original-coordinate C² displacement bound
`5ε/32`, not absorbed into an unproved reserve.

Only the finite reference C² bound `Bref` enters the additional initial-scale
threshold. Higher orders enter through the increasing stages and the actual
increment estimates. This is still conditional on the geometric one-step
provider's actual increments and defect identities, not a construction of
that provider or a full acceptance claim for `thm:repair`. -/
theorem repair_series_limit_with_scaled_initialization
    (a : E ≃L[ℝ] (Fin n → ℝ))
    (hdim : 2 ≤ Module.finrank ℝ E) (lam bound m L R Bref : ℝ)
    (hlam : 0 < lam) (hm : 0 < m) (hR : 0 ≤ R) (hBref : 0 ≤ Bref)
    (hcast : ∀ x : M, ‖(tangentSpaceCastModel I x).toContinuousLinearMap‖ ≤ R) :
    ∃ ε : ℝ, 0 < ε ∧
    ∀ (F0 : M → EuclideanSpace ℝ (Fin N))
      (_hF0 : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F0)
      (f : ℕ → M → EuclideanSpace ℝ (Fin N)) (stage : ℕ → ℕ)
      (t : ℝ) (g : ∀ x : M, LinearMap.BilinForm ℝ (TangentSpace I x))
      (Hseq : ℕ → ∀ x : M, LinearMap.BilinForm ℝ (TangentSpace I x))
      (ξ : ∀ x : M, TangentSpace I x →L[ℝ] ℝ)
      (e : ∀ x : M, (ξ x).ker ≃L[ℝ] V)
      (S : M → SymmetricSquare V →L[ℝ] EuclideanSpace ℝ (Fin N)),
      Tendsto stage atTop atTop → (∀ j, 10 ≤ stage j) →
      0 < t → t ≤ (1 / 2 : ℝ) ^ (5 : ℕ) → t ≤ ε / (32 * (Bref + 1)) →
      (∀ x : M, ∃ O T U : Set (Fin n → ℝ),
        IsOpen O ∧ T ⊆ O ∧ IsOpen U ∧ U ⊆ T ∧ a (extChartAt I x x) ∈ U ∧
        ContDiffOn ℝ ∞ (euclideanCoordinateRepresentative a (F0 ∘ (extChartAt I x).symm)) O ∧
        paperCoordinateCj 2 (euclideanCoordinateRepresentative a (F0 ∘ (extChartAt I x).symm))
          O T ≤ ENNReal.ofReal Bref ∧
        (∀ j, ContDiffOn ℝ ∞
          (euclideanCoordinateRepresentative a (f j ∘ (extChartAt I x).symm)) O) ∧
        (∀ j, paperCoordinateCj (stage j / 2)
          (euclideanCoordinateRepresentative a (f j ∘ (extChartAt I x).symm)) O T ≤
            ENNReal.ofReal ((ε / 8) * iterationScale t j))) →
      (∀ (x : M) (v w : TangentSpace I x),
        ∃ C : ℝ, ∀ᶠ j in atTop, ‖Hseq j x v w‖ ≤ C) →
      (∀ j x, g x - inducedMetric (I := I)
        (fun y ↦ Real.sqrt (1 - (t ^ (10 : ℕ)) ^ 2) • F0 y +
          ∑ i ∈ Finset.range j, f i y) x =
            (iterationScale t j ^ stage j) ^ 2 • Hseq j x) →
      (∀ x v, lam * ‖v‖ ^ 2 ≤ ‖mvfderiv I F0 x v‖ ^ 2) →
      (∀ x, ‖actualCoordinateSecondJet (I := I) F0 x‖ ≤ bound) →
      (∀ x, ‖ξ x‖ = 1) → (∀ x, ‖(e x).symm.toContinuousLinearMap‖ ≤ L) →
      (∀ x, covectorRestriction
        (E := TangentSpace I x) (F := EuclideanSpace ℝ (Fin N))
        ((LinearMap.range (mvfderiv I F0 x).toLinearMap)ᗮ.starProjection.comp
          (actualCoordinateSecondJet (I := I) F0 x)) (ξ x) =
          (S x).comp (symmetricSquareMapL (e x).toContinuousLinearMap)) →
      (∀ x z, m * ‖z‖ ≤ ‖S x z‖) →
      let Fstar : M → EuclideanSpace ℝ (Fin N) :=
        fun x ↦ Real.sqrt (1 - (t ^ (10 : ℕ)) ^ 2) • F0 x + ∑' j, f j x
      (∀ x, Summable (fun j ↦ f j x)) ∧
      ∃ hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ Fstar,
        inducedMetric (I := I) Fstar = g ∧ PhaseRegular Fstar hF ∧
        (∀ x, (∀ v, (lam / 4) * ‖v‖ ^ 2 ≤ ‖mvfderiv I Fstar x v‖ ^ 2) ∧
          m / (2 * (1 + L ^ 2)) ≤ truePhaseMargin Fstar hF x) ∧
        (∀ x : M, ∃ U : Set (Fin n → ℝ),
          IsOpen U ∧ a (extChartAt I x x) ∈ U ∧
          paperCoordinateCj 2 (euclideanCoordinateRepresentative a
            ((fun y ↦ Fstar y - F0 y) ∘ (extChartAt I x).symm)) U U ≤
              ENNReal.ofReal (5 * ε / 32)) := by
  obtain ⟨ε, hε, hphase⟩ := phase_regular_of_paperCoordinateC2_budget
    (I := I) (M := M) (V := V) (N := N) a hdim lam bound m L R hlam hm hR hcast
  refine ⟨ε, hε, ?_⟩
  intro F0 hF0 f stage t g Hseq ξ e S hstage hmin ht htsmall htbudget hchart hH hdefect
    hA hQ hξ hinv hselector hS
  let Fstar : M → EuclideanSpace ℝ (Fin N) :=
    fun x ↦ Real.sqrt (1 - (t ^ (10 : ℕ)) ^ 2) • F0 x + ∑' j, f j x
  have ht1 : t < 1 := by norm_num at htsmall ⊢; linarith
  have hscaledSmooth : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
      (fun x ↦ Real.sqrt (1 - (t ^ (10 : ℕ)) ^ 2) • F0 x) := by
    have hc : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun _ : M ↦ Real.sqrt (1 - (t ^ (10 : ℕ)) ^ 2)) := contMDiff_const
    exact hc.smul hF0
  have hmetric := smooth_repair_series_metric_limit_of_paper_stage_bounds a
    (fun x ↦ Real.sqrt (1 - (t ^ (10 : ℕ)) ^ 2) • F0 x) f stage
    (fun j ↦ iterationScale t j ^ stage j) g Hseq
    hscaledSmooth hstage ht ht1
    (fun x ↦ by
      obtain ⟨O, T, U, hO, hTO, hU, hUT, hx, _hF, _href, hf, hb⟩ := hchart x
      exact ⟨O, T, U, hO, hTO, hU, hUT, hx, hf, ε / 8, by positivity, hb⟩)
    (tendsto_repair_defect_scale_zero ht ht1 stage hmin) hH hdefect
  have hbudget (x : M) : ∃ U : Set (Fin n → ℝ),
      IsOpen U ∧ a (extChartAt I x x) ∈ U ∧
      ContDiffOn ℝ ∞ (euclideanCoordinateRepresentative a
        ((fun y ↦ Fstar y - F0 y) ∘ (extChartAt I x).symm)) U ∧
      paperCoordinateCj 2 (euclideanCoordinateRepresentative a
        ((fun y ↦ Fstar y - F0 y) ∘ (extChartAt I x).symm)) U U ≤
          ENNReal.ofReal (5 * ε / 32) := by
    obtain ⟨O, T, U, hO, hTO, hU, hUT, hx, hF, href, hf, hb⟩ := hchart x
    have hsum := repair_displacement_euclidean_on_inner_buffer a
      (F0 ∘ (extChartAt I x).symm) (fun j ↦ f j ∘ (extChartAt I x).symm) stage
      hO hTO hU hUT hF hf hstage (fun j ↦ by have := hmin j; omega)
      ht htsmall hε hBref htbudget href hb
    refine ⟨U, hU, hx, ?_, ?_⟩
    · simpa only [Fstar, euclideanCoordinateRepresentative, Function.comp_def,
        map_sub] using hsum.1.sub (hF.mono (hUT.trans hTO))
    · simpa only [Fstar, Function.comp_def] using hsum.2
  have hp := hphase F0 Fstar hF0 hmetric.2.1 ξ e S hA hQ
    (fun x ↦ by
      obtain ⟨U, hU, hx, hsmooth, hb⟩ := hbudget x
      exact ⟨U, U, U, hU, Subset.rfl, hU, Subset.rfl, hx, hsmooth,
        hb.trans (ENNReal.ofReal_le_ofReal (by linarith))⟩)
    hξ hinv hselector hS
  refine ⟨hmetric.1, hmetric.2.1, hmetric.2.2, hp.1, hp.2, ?_⟩
  intro x
  obtain ⟨U, hU, hx, _hsmooth, hb⟩ := hbudget x
  exact ⟨U, hU, hx, hb⟩

end ReferenceBase

#print axioms euclideanCoordinateRepresentative_tsum
#print axioms paperCoordinateC2_tsum_on_inner_buffer
#print axioms repair_displacement_euclidean_on_inner_buffer
#print axioms repair_series_limit_with_reference_base
#print axioms repair_series_limit_with_scaled_initialization

end GlobalEmbedding.Offline
