import GlobalEmbedding.Offline.ActualHessianJet
import GlobalEmbedding.Paper.PhaseRegularMargin
import GlobalEmbedding.Paper.GeneralChartContDiff

/-!
# Retaining the actual phase condition from actual coordinate two-jet budgets

Source: `literature/parallelizable-stable-plus-one/main.tex`, `thm:repair`
line 776 and the selector-margin stability in `prop:initialization`.

This module applies the original `initialization_phase_stability` theorem with
the actual first differential and the explicitly constructed actual second jet.
There are no independent candidate second jets or assumed jet-identification
equalities. The conclusion is the repository's original `PhaseRegular` predicate.
-/

open Manifold Bundle GlobalEmbedding.Paper
open scoped TensorProduct ContDiff Topology

namespace GlobalEmbedding.Offline

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance actualPhaseSquareRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance actualPhaseSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {E H M V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [RiemannianBundle (TangentSpace I : M → Type _)]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] {N : ℕ}

/-- True coordinate derivative budgets preserve the true phase margin and
actual phase regularity. All first and second jets are constructed from the two
displayed maps, using the original Riemannian tangent norms and quotient norm.

The derivative budgets include the explicit source-chart transport norm and the
fixed actual Hessian-lift constant. Thus this theorem can consume a genuine C²
coordinate budget after the quantitative norm comparison, with no assumed bound
on an independently supplied `Q'`. Reference ellipticity and selector reserves
are exactly the fixed geometric reserves of the original stability theorem. -/
theorem phase_regular_of_actual_two_jet_budget
    (hdim : 2 ≤ Module.finrank ℝ E) (lam bound m L : ℝ)
    (hlam : 0 < lam) (hm : 0 < m) :
    ∃ δ : ℝ, 0 < δ ∧
    ∀ (F0 F : M → EuclideanSpace ℝ (Fin N))
      (_hF0 : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F0)
      (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
      (ξ : ∀ x : M, TangentSpace I x →L[ℝ] ℝ)
      (e : ∀ x : M, (ξ x).ker ≃L[ℝ] V)
      (S : M → SymmetricSquare V →L[ℝ] EuclideanSpace ℝ (Fin N)),
      (∀ x v, lam * ‖v‖ ^ 2 ≤ ‖mvfderiv I F0 x v‖ ^ 2) →
      (∀ x, ‖actualCoordinateSecondJet (I := I) F0 x‖ ≤ bound) →
      (∀ x, ‖iteratedFDeriv ℝ 1 ((fun y ↦ F y - F0 y) ∘ (extChartAt I x).symm)
          (extChartAt I x x)‖ * ‖(tangentSpaceCastModel I x).toContinuousLinearMap‖ ≤ δ) →
      (∀ x, actualHessianLiftConstant E (EuclideanSpace ℝ (Fin N)) *
          ‖iteratedFDeriv ℝ 2 ((fun y ↦ F y - F0 y) ∘ (extChartAt I x).symm)
            (extChartAt I x x)‖ * ‖(tangentSpaceCastModel I x).toContinuousLinearMap‖ ^ 2 ≤ δ) →
      (∀ x, ‖ξ x‖ = 1) → (∀ x, ‖(e x).symm.toContinuousLinearMap‖ ≤ L) →
      (∀ x, covectorRestriction
        (E := TangentSpace I x) (F := EuclideanSpace ℝ (Fin N))
        ((LinearMap.range (mvfderiv I F0 x).toLinearMap)ᗮ.starProjection.comp
          (actualCoordinateSecondJet (I := I) F0 x)) (ξ x) =
          (S x).comp (symmetricSquareMapL (e x).toContinuousLinearMap)) →
      (∀ x z, m * ‖z‖ ≤ ‖S x z‖) →
      PhaseRegular F hF ∧
      ∀ x, (∀ v, (lam / 4) * ‖v‖ ^ 2 ≤ ‖mvfderiv I F x v‖ ^ 2) ∧
        m / (2 * (1 + L ^ 2)) ≤ truePhaseMargin F hF x := by
  obtain ⟨δ, hδ, hstable⟩ := initialization_phase_stability
    (I := I) (M := M) (V := V) (N := N) hdim lam bound m L hlam hm
  refine ⟨δ, hδ, ?_⟩
  intro F0 F hF0 hF ξ e S hA hQ hD1 hD2 hξ hinv hselector hS
  have hF0coord (x : M) : ContDiffAt ℝ 2 (F0 ∘ (extChartAt I x).symm) (extChartAt I x x) :=
    (contDiffAt_general_chart_representative (hF0 x)).of_le (by simp)
  have hFcoord (x : M) : ContDiffAt ℝ 2 (F ∘ (extChartAt I x).symm) (extChartAt I x x) :=
    (contDiffAt_general_chart_representative (hF x)).of_le (by simp)
  have hAB (x : M) : ‖mvfderiv I F0 x - mvfderiv I F x‖ ≤ δ := by
    have hrev := ContinuousLinearMap.opNorm_neg (mvfderiv I F0 x - mvfderiv I F x)
    simp only [neg_sub] at hrev
    exact hrev.symm.trans_le
      ((mvfderiv_sub_norm_le_of_contDiffAt (hFcoord x) (hF0coord x)).trans (hD1 x))
  have hDQ (x : M) :
      ‖actualCoordinateSecondJet (I := I) F x - actualCoordinateSecondJet (I := I) F0 x‖ ≤ δ :=
    (actualCoordinateSecondJet_sub_norm_le (hFcoord x) (hF0coord x)).trans (hD2 x)
  have h := hstable F hF (mvfderiv I F0) (mvfderiv I F)
    (actualCoordinateSecondJet (I := I) F0) (actualCoordinateSecondJet (I := I) F)
    ξ e S hA hQ hAB hDQ hξ hinv hselector hS (fun _ ↦ rfl)
    (fun x v w ↦ actualCoordinateSecondJet_product (hFcoord x) v w)
  have hmargin (x : M) : m / (2 * (1 + L ^ 2)) ≤ truePhaseMargin F hF x :=
    (h x).2.2.2.1
  refine ⟨(phase_regular_iff_positive_true_margin hdim F hF).mpr ?_,
    fun x ↦ ⟨(h x).1, hmargin x⟩⟩
  intro x
  exact (div_pos hm (by positivity : 0 < 2 * (1 + L ^ 2))).trans_le (hmargin x)

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [IsManifold I ∞ M] [BoundarylessManifold I M] in
/-- A bound in the ORIGINAL componentwise C² norm controls the two actual
derivative budgets needed above. This explicitly keeps the finite norm domain,
inner buffer, Euclidean target conversion and Riemannian chart-transport factor. -/
theorem actual_two_jet_bounds_of_paperCoordinateC2
    {n : ℕ} (a : E ≃L[ℝ] (Fin n → ℝ))
    (u : M → EuclideanSpace ℝ (Fin N)) (x : M)
    {O S U : Set (Fin n → ℝ)}
    (hO : IsOpen O) (hSO : S ⊆ O) (hU : IsOpen U) (hUS : U ⊆ S)
    (hx : a (extChartAt I x x) ∈ U)
    (hu : ContDiffOn ℝ ∞ (euclideanCoordinateRepresentative a (u ∘ (extChartAt I x).symm)) O)
    {B R : ℝ} (hB : 0 ≤ B)
    (hcast : ‖(tangentSpaceCastModel I x).toContinuousLinearMap‖ ≤ R)
    (hbound : paperCoordinateCj 2
      (euclideanCoordinateRepresentative a (u ∘ (extChartAt I x).symm)) O S ≤ ENNReal.ofReal B) :
    (‖iteratedFDeriv ℝ 1 (u ∘ (extChartAt I x).symm) (extChartAt I x x)‖ *
        ‖(tangentSpaceCastModel I x).toContinuousLinearMap‖ ≤
      (‖(EuclideanSpace.equiv (Fin N) ℝ).symm.toContinuousLinearMap‖ *
        (n : ℝ) * ‖a.toContinuousLinearMap‖ * R) * B) ∧
    (actualHessianLiftConstant E (EuclideanSpace ℝ (Fin N)) *
        ‖iteratedFDeriv ℝ 2 (u ∘ (extChartAt I x).symm) (extChartAt I x x)‖ *
          ‖(tangentSpaceCastModel I x).toContinuousLinearMap‖ ^ 2 ≤
      (actualHessianLiftConstant E (EuclideanSpace ℝ (Fin N)) *
        ‖(EuclideanSpace.equiv (Fin N) ℝ).symm.toContinuousLinearMap‖ *
          (n : ℝ) ^ 2 * ‖a.toContinuousLinearMap‖ ^ 2 * R ^ 2) * B) := by
  have hjet (k : ℕ) (hk : k ≤ 2) :
      ‖iteratedFDeriv ℝ k (u ∘ (extChartAt I x).symm) (extChartAt I x x)‖ ≤
        ‖(EuclideanSpace.equiv (Fin N) ℝ).symm.toContinuousLinearMap‖ *
          ((n : ℝ) ^ k * B) * ‖a.toContinuousLinearMap‖ ^ k := by
    have h := iteratedFDerivWithin_le_of_euclidean_coordinate_bound a
      (u ∘ (extChartAt I x).symm) hO hSO hU hUS hu hB hbound hk hx
    simpa only [iteratedFDerivWithin_of_isOpen k (hU.preimage a.continuous) hx] using h
  have hH : 0 ≤ actualHessianLiftConstant E (EuclideanSpace ℝ (Fin N)) :=
    actualHessianLiftConstant_nonneg
  refine ⟨?_, ?_⟩
  · have h := mul_le_mul (hjet 1 (by omega)) hcast
      (ContinuousLinearMap.opNorm_nonneg _) (by positivity)
    convert h using 1; ring
  · have hcast2 := pow_le_pow_left₀ (ContinuousLinearMap.opNorm_nonneg _) hcast 2
    have h := mul_le_mul (mul_le_mul_of_nonneg_left (hjet 2 le_rfl) hH) hcast2
      (sq_nonneg _) (by positivity)
    convert h using 1; ring

/-- A genuine small budget in the ORIGINAL paper C² norm retains actual phase
regularity, with a uniform quantitative true margin.

The tolerance is chosen before the perturbing map, from the fixed reference
ellipticity/selector reserves, the actual source coordinate equivalence, the
canonical Euclidean conversion, and a displayed uniform bound for the native
chart tangent identifications. Each point may use its own original outer
differentiation domain, finite norm domain, and inner open buffer. No chart-count
factor or artificial second-jet variable is introduced.
-/
theorem phase_regular_of_paperCoordinateC2_budget
    {n : ℕ} (a : E ≃L[ℝ] (Fin n → ℝ))
    (hdim : 2 ≤ Module.finrank ℝ E) (lam bound m L R : ℝ)
    (hlam : 0 < lam) (hm : 0 < m) (hR : 0 ≤ R)
    (hcast : ∀ x : M, ‖(tangentSpaceCastModel I x).toContinuousLinearMap‖ ≤ R) :
    ∃ ε : ℝ, 0 < ε ∧
    ∀ (F0 F : M → EuclideanSpace ℝ (Fin N))
      (_hF0 : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F0)
      (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
      (ξ : ∀ x : M, TangentSpace I x →L[ℝ] ℝ)
      (e : ∀ x : M, (ξ x).ker ≃L[ℝ] V)
      (S : M → SymmetricSquare V →L[ℝ] EuclideanSpace ℝ (Fin N)),
      (∀ x v, lam * ‖v‖ ^ 2 ≤ ‖mvfderiv I F0 x v‖ ^ 2) →
      (∀ x, ‖actualCoordinateSecondJet (I := I) F0 x‖ ≤ bound) →
      (∀ x : M, ∃ O T U : Set (Fin n → ℝ),
        IsOpen O ∧ T ⊆ O ∧ IsOpen U ∧ U ⊆ T ∧ a (extChartAt I x x) ∈ U ∧
        ContDiffOn ℝ ∞
          (euclideanCoordinateRepresentative a ((fun y ↦ F y - F0 y) ∘ (extChartAt I x).symm)) O ∧
        paperCoordinateCj 2
          (euclideanCoordinateRepresentative a ((fun y ↦ F y - F0 y) ∘ (extChartAt I x).symm)) O T ≤
            ENNReal.ofReal ε) →
      (∀ x, ‖ξ x‖ = 1) → (∀ x, ‖(e x).symm.toContinuousLinearMap‖ ≤ L) →
      (∀ x, covectorRestriction
        (E := TangentSpace I x) (F := EuclideanSpace ℝ (Fin N))
        ((LinearMap.range (mvfderiv I F0 x).toLinearMap)ᗮ.starProjection.comp
          (actualCoordinateSecondJet (I := I) F0 x)) (ξ x) =
          (S x).comp (symmetricSquareMapL (e x).toContinuousLinearMap)) →
      (∀ x z, m * ‖z‖ ≤ ‖S x z‖) →
      PhaseRegular F hF ∧
      ∀ x, (∀ v, (lam / 4) * ‖v‖ ^ 2 ≤ ‖mvfderiv I F x v‖ ^ 2) ∧
        m / (2 * (1 + L ^ 2)) ≤ truePhaseMargin F hF x := by
  obtain ⟨δ, hδ, hstable⟩ := phase_regular_of_actual_two_jet_budget
    (I := I) (M := M) (V := V) (N := N) hdim lam bound m L hlam hm
  let C1 : ℝ := ‖(EuclideanSpace.equiv (Fin N) ℝ).symm.toContinuousLinearMap‖ *
    (n : ℝ) * ‖a.toContinuousLinearMap‖ * R
  let C2 : ℝ := actualHessianLiftConstant E (EuclideanSpace ℝ (Fin N)) *
    ‖(EuclideanSpace.equiv (Fin N) ℝ).symm.toContinuousLinearMap‖ *
      (n : ℝ) ^ 2 * ‖a.toContinuousLinearMap‖ ^ 2 * R ^ 2
  have hH : 0 ≤ actualHessianLiftConstant E (EuclideanSpace ℝ (Fin N)) :=
    actualHessianLiftConstant_nonneg
  have hC1 : 0 ≤ C1 := by dsimp [C1]; positivity
  have hC2 : 0 ≤ C2 := by dsimp [C2]; positivity
  let C : ℝ := 1 + C1 + C2
  have hC : 0 < C := by dsimp [C]; linarith
  let ε : ℝ := δ / C
  have hε : 0 < ε := div_pos hδ hC
  have hCε : C * ε = δ := by dsimp [ε]; field_simp
  have hC1ε : C1 * ε ≤ δ := by
    apply (mul_le_mul_of_nonneg_right (show C1 ≤ C by dsimp [C]; linarith) hε.le).trans_eq
    exact hCε
  have hC2ε : C2 * ε ≤ δ := by
    apply (mul_le_mul_of_nonneg_right (show C2 ≤ C by dsimp [C]; linarith) hε.le).trans_eq
    exact hCε
  refine ⟨ε, hε, ?_⟩
  intro F0 F hF0 hF ξ e S hA hQ hbudget hξ hinv hselector hS
  have hD (x : M) :
      (‖iteratedFDeriv ℝ 1 ((fun y ↦ F y - F0 y) ∘ (extChartAt I x).symm)
          (extChartAt I x x)‖ * ‖(tangentSpaceCastModel I x).toContinuousLinearMap‖ ≤ C1 * ε) ∧
      (actualHessianLiftConstant E (EuclideanSpace ℝ (Fin N)) *
          ‖iteratedFDeriv ℝ 2 ((fun y ↦ F y - F0 y) ∘ (extChartAt I x).symm)
            (extChartAt I x x)‖ * ‖(tangentSpaceCastModel I x).toContinuousLinearMap‖ ^ 2 ≤ C2 * ε) := by
    obtain ⟨O, T, U, hO, hTO, hU, hUT, hx, hsmooth, hnorm⟩ := hbudget x
    exact actual_two_jet_bounds_of_paperCoordinateC2 a (fun y ↦ F y - F0 y) x
      hO hTO hU hUT hx hsmooth hε.le (hcast x) hnorm
  exact hstable F0 F hF0 hF ξ e S hA hQ
    (fun x ↦ (hD x).1.trans hC1ε) (fun x ↦ (hD x).2.trans hC2ε)
    hξ hinv hselector hS

#print axioms phase_regular_of_actual_two_jet_budget
#print axioms actual_two_jet_bounds_of_paperCoordinateC2
#print axioms phase_regular_of_paperCoordinateC2_budget

end GlobalEmbedding.Offline
