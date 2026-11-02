import GlobalEmbedding.Offline.ActualPhaseStability

/-!+# Actual source two-jets and phase margins from joint coordinate budgets

Source: `thm:repair`, main.tex lines 776–778. The source slice is the actual
map with its parameter fixed. Its derivatives insert zero parameter directions
into the actual joint derivatives. The induced metric and true phase condition
continue to use the original source tangent bundle, never a product metric.

The total C² budgets below concern convergence and stability. They do not
identify total C^(j+2) smoothing norms with the manuscript's spatial two-jet
followed by j total derivatives; that distinct analytic interface is unchanged.
-/

open Set Manifold Bundle GlobalEmbedding.Paper
open scoped ContDiff TensorProduct Topology ENNReal

namespace GlobalEmbedding.Offline

section NativeSlices

variable {EP E F : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Every actual derivative of a fixed-parameter slice is the actual joint
derivative restricted by native `inr`, hence zero parameter vectors in every
slot. Smoothness is needed only on the displayed open joint neighborhood. -/
theorem iteratedFDeriv_source_slice
    {u : EP × E → F} {U : Set (EP × E)} (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ u U) (k : ℕ) {p : EP} {x : E} (hx : (p, x) ∈ U) :
    iteratedFDeriv ℝ k (fun y ↦ u (p, y)) x =
      (iteratedFDeriv ℝ k u (p, x)).compContinuousLinearMap
        (fun _ : Fin k ↦ ContinuousLinearMap.inr ℝ EP E) := by
  let V : Set (EP × E) := (fun z : EP × E ↦ (p, 0) + z) ⁻¹' U
  have hV : IsOpen V := hU.preimage (continuous_const.add continuous_id)
  have hshift : ContDiffOn ℝ ∞ (fun z : EP × E ↦ u ((p, 0) + z)) V :=
    hu.comp (contDiffOn_const.add contDiffOn_id) (fun _ hz ↦ hz)
  let inc : E →L[ℝ] EP × E := ContinuousLinearMap.inr ℝ EP E
  have hpre : IsOpen (inc ⁻¹' V) := hV.preimage inc.continuous
  have hinc : inc x ∈ V := by simpa [V, inc] using hx
  have h := inc.iteratedFDerivWithin_comp_right hshift hV.uniqueDiffOn
    hpre.uniqueDiffOn hinc (i := k) (by simp)
  rw [iteratedFDerivWithin_of_isOpen k hpre hinc,
    iteratedFDerivWithin_of_isOpen k hV hinc] at h
  simpa only [inc, Function.comp_def, ContinuousLinearMap.inr_apply,
    iteratedFDeriv_comp_add_left, Prod.mk_add_mk, add_zero, zero_add] using h

/-- Actual source derivatives have no larger operator norm than the joint
derivatives: native source inclusion has norm at most one, in every dimension. -/
theorem norm_iteratedFDeriv_source_slice_le
    {u : EP × E → F} {U : Set (EP × E)} (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ u U) (k : ℕ) {p : EP} {x : E} (hx : (p, x) ∈ U) :
    ‖iteratedFDeriv ℝ k (fun y ↦ u (p, y)) x‖ ≤ ‖iteratedFDeriv ℝ k u (p, x)‖ := by
  rw [iteratedFDeriv_source_slice hU hu k hx]
  have h := (iteratedFDeriv ℝ k u (p, x)).norm_compContinuousLinearMap_le
    (fun _ : Fin k ↦ ContinuousLinearMap.inr ℝ EP E)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  apply h.trans
  apply mul_le_of_le_one_right (norm_nonneg _)
  simpa only [one_pow] using pow_le_pow_left₀
    (ContinuousLinearMap.opNorm_nonneg (ContinuousLinearMap.inr ℝ EP E))
    (ContinuousLinearMap.norm_inr_le_one (𝕜 := ℝ) (E := EP) (F := E)) k

end NativeSlices

section ActualProductCharts

variable {EP E HP H P M F : Type*}
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {J : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- The literal source chart representative is the actual product chart
representative with the parameter coordinate fixed at its center. The identity
uses the real chart inverse, including its exact inverse value at that center. -/
theorem source_chart_eq_joint_chart_slice (u : P × M → F) (p : P) (x : M) :
    (fun y ↦ u (p, y)) ∘ (extChartAt I x).symm =
      fun y ↦ (u ∘ (extChartAt (J.prod I) (p, x)).symm) (extChartAt J p p, y) := by
  funext y
  simp only [Function.comp_apply, extChartAt_prod, PartialEquiv.prod_coe_symm,
    extChartAt_to_inv]

/-- The native source-chart jet of the actual slice is bounded by the native
joint-chart jet of the same actual map, on an honest open joint buffer. -/
theorem source_chart_iteratedFDeriv_norm_le_joint
    (u : P × M → F) (p : P) (x : M) {U : Set (EP × E)}
    (hU : IsOpen U) (hx : extChartAt (J.prod I) (p, x) (p, x) ∈ U)
    (hu : ContDiffOn ℝ ∞ (u ∘ (extChartAt (J.prod I) (p, x)).symm) U) (k : ℕ) :
    ‖iteratedFDeriv ℝ k ((fun y ↦ u (p, y)) ∘ (extChartAt I x).symm) (extChartAt I x x)‖ ≤
      ‖iteratedFDeriv ℝ k (u ∘ (extChartAt (J.prod I) (p, x)).symm)
        (extChartAt (J.prod I) (p, x) (p, x))‖ := by
  rw [source_chart_eq_joint_chart_slice (J := J) u p x]
  have hcenter : extChartAt (J.prod I) (p, x) (p, x) =
      (extChartAt J p p, extChartAt I x x) := by
    rw [extChartAt_prod]
    rfl
  rw [hcenter] at hx ⊢
  exact norm_iteratedFDeriv_source_slice_le hU hu k hx

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- The ORIGINAL joint coordinate norm controls the actual source-slice jet.
Its only conversion constants are the real target equivalence, joint coordinate
dimension, and joint source equivalence; source restriction loses no factor. -/
theorem source_chart_jet_le_of_joint_paperCoordinateCj
    {n N : ℕ} (a : (EP × E) ≃L[ℝ] (Fin n → ℝ))
    (u : P × M → EuclideanSpace ℝ (Fin N)) (p : P) (x : M)
    {O S U : Set (Fin n → ℝ)}
    (hO : IsOpen O) (hSO : S ⊆ O) (hU : IsOpen U) (hUS : U ⊆ S)
    (hx : a (extChartAt (J.prod I) (p, x) (p, x)) ∈ U)
    (hu : ContDiffOn ℝ ∞ (euclideanCoordinateRepresentative a
      (u ∘ (extChartAt (J.prod I) (p, x)).symm)) O)
    {j k : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hbound : paperCoordinateCj j (euclideanCoordinateRepresentative a
      (u ∘ (extChartAt (J.prod I) (p, x)).symm)) O S ≤ ENNReal.ofReal B)
    (hk : k ≤ j) :
    ‖iteratedFDeriv ℝ k ((fun y ↦ u (p, y)) ∘ (extChartAt I x).symm) (extChartAt I x x)‖ ≤
      ‖(EuclideanSpace.equiv (Fin N) ℝ).symm.toContinuousLinearMap‖ *
        ((n : ℝ) ^ k * B) * ‖a.toContinuousLinearMap‖ ^ k := by
  have hpre := hU.preimage a.continuous
  have hsmooth := contDiffOn_of_euclideanCoordinateRepresentative a
    (u ∘ (extChartAt (J.prod I) (p, x)).symm) (hUS.trans hSO) hu
  have hjoint := iteratedFDerivWithin_le_of_euclidean_coordinate_bound a
    (u ∘ (extChartAt (J.prod I) (p, x)).symm) hO hSO hU hUS hu hB hbound hk hx
  rw [iteratedFDerivWithin_of_isOpen k hpre hx] at hjoint
  exact (source_chart_iteratedFDeriv_norm_le_joint u p x hpre hx hsmooth k).trans hjoint

end ActualProductCharts

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance parametricPhaseSquareRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance parametricPhaseSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

section ParametricPhase

variable {EP E HP H P M V : Type*}
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {J : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [RiemannianBundle (TangentSpace I : M → Type _)]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n N : ℕ}

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [IsManifold I ∞ M] [BoundarylessManifold I M] in
/-- A genuine joint original C² norm budget controls the source-slice first
differential and actual source Hessian-lift budgets. Only the SOURCE tangent
transport and the SOURCE symmetric-square lift occur; no product Riemannian
structure or arbitrary surrogate second jet is introduced. -/
theorem source_two_jet_bounds_of_joint_paperCoordinateC2
    (a : (EP × E) ≃L[ℝ] (Fin n → ℝ))
    (u : P × M → EuclideanSpace ℝ (Fin N)) (p : P) (x : M)
    {O S U : Set (Fin n → ℝ)}
    (hO : IsOpen O) (hSO : S ⊆ O) (hU : IsOpen U) (hUS : U ⊆ S)
    (hx : a (extChartAt (J.prod I) (p, x) (p, x)) ∈ U)
    (hu : ContDiffOn ℝ ∞ (euclideanCoordinateRepresentative a
      (u ∘ (extChartAt (J.prod I) (p, x)).symm)) O)
    {B R : ℝ} (hB : 0 ≤ B)
    (hcast : ‖(tangentSpaceCastModel I x).toContinuousLinearMap‖ ≤ R)
    (hbound : paperCoordinateCj 2 (euclideanCoordinateRepresentative a
      (u ∘ (extChartAt (J.prod I) (p, x)).symm)) O S ≤ ENNReal.ofReal B) :
    (‖iteratedFDeriv ℝ 1 ((fun y ↦ u (p, y)) ∘ (extChartAt I x).symm) (extChartAt I x x)‖ *
        ‖(tangentSpaceCastModel I x).toContinuousLinearMap‖ ≤
      (‖(EuclideanSpace.equiv (Fin N) ℝ).symm.toContinuousLinearMap‖ *
        (n : ℝ) * ‖a.toContinuousLinearMap‖ * R) * B) ∧
    (actualHessianLiftConstant E (EuclideanSpace ℝ (Fin N)) *
        ‖iteratedFDeriv ℝ 2 ((fun y ↦ u (p, y)) ∘ (extChartAt I x).symm) (extChartAt I x x)‖ *
          ‖(tangentSpaceCastModel I x).toContinuousLinearMap‖ ^ 2 ≤
      (actualHessianLiftConstant E (EuclideanSpace ℝ (Fin N)) *
        ‖(EuclideanSpace.equiv (Fin N) ℝ).symm.toContinuousLinearMap‖ *
          (n : ℝ) ^ 2 * ‖a.toContinuousLinearMap‖ ^ 2 * R ^ 2) * B) := by
  have hjet (k : ℕ) (hk : k ≤ 2) :=
    source_chart_jet_le_of_joint_paperCoordinateCj a u p x hO hSO hU hUS hx hu hB hbound hk
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


/-- One tolerance in the ORIGINAL joint C² coordinate norm retains the original
source phase condition for every parameter, with a common quantitative true
margin. Every reference differential and symmetric-square Hessian belongs to
the source slice. The parameter variable never enters the metric tangent space.

The proof first establishes the actual source two-jet bounds above, then uses
ONE tolerance from the original phase-stability theorem for all parameters.
Joint smoothness supplies native smoothness of each literal slice. -/
theorem parametric_phase_regular_of_joint_paperCoordinateC2_budget
    (a : (EP × E) ≃L[ℝ] (Fin n → ℝ))
    (hdim : 2 ≤ Module.finrank ℝ E) (lam bound m L R : ℝ)
    (hlam : 0 < lam) (hm : 0 < m) (hR : 0 ≤ R)
    (hcast : ∀ x : M, ‖(tangentSpaceCastModel I x).toContinuousLinearMap‖ ≤ R) :
    ∃ ε : ℝ, 0 < ε ∧
    ∀ (F0 F : P × M → EuclideanSpace ℝ (Fin N))
      (_hF0 : ContMDiff (J.prod I) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F0)
      (_hF : ContMDiff (J.prod I) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
      (ξ : ∀ _p : P, ∀ x : M, TangentSpace I x →L[ℝ] ℝ)
      (e : ∀ p x, (ξ p x).ker ≃L[ℝ] V)
      (S : P → M → SymmetricSquare V →L[ℝ] EuclideanSpace ℝ (Fin N)),
      (∀ p x v, lam * ‖v‖ ^ 2 ≤ ‖mvfderiv I (fun y ↦ F0 (p, y)) x v‖ ^ 2) →
      (∀ p x, ‖actualCoordinateSecondJet (I := I) (fun y ↦ F0 (p, y)) x‖ ≤ bound) →
      (∀ z : P × M, ∃ O T U : Set (Fin n → ℝ),
        IsOpen O ∧ T ⊆ O ∧ IsOpen U ∧ U ⊆ T ∧ a (extChartAt (J.prod I) z z) ∈ U ∧
        ContDiffOn ℝ ∞ (euclideanCoordinateRepresentative a
          ((fun w ↦ F w - F0 w) ∘ (extChartAt (J.prod I) z).symm)) O ∧
        paperCoordinateCj 2 (euclideanCoordinateRepresentative a
          ((fun w ↦ F w - F0 w) ∘ (extChartAt (J.prod I) z).symm)) O T ≤
            ENNReal.ofReal ε) →
      (∀ p x, ‖ξ p x‖ = 1) → (∀ p x, ‖(e p x).symm.toContinuousLinearMap‖ ≤ L) →
      (∀ p x, covectorRestriction
        (E := TangentSpace I x) (F := EuclideanSpace ℝ (Fin N))
        ((LinearMap.range (mvfderiv I (fun y ↦ F0 (p, y)) x).toLinearMap)ᗮ.starProjection.comp
          (actualCoordinateSecondJet (I := I) (fun y ↦ F0 (p, y)) x)) (ξ p x) =
          (S p x).comp (symmetricSquareMapL (e p x).toContinuousLinearMap)) →
      (∀ p x z, m * ‖z‖ ≤ ‖S p x z‖) →
      ∀ p, ∃ hFp : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (fun x ↦ F (p, x)),
        PhaseRegular (fun x ↦ F (p, x)) hFp ∧
        ∀ x, (∀ v, (lam / 4) * ‖v‖ ^ 2 ≤ ‖mvfderiv I (fun y ↦ F (p, y)) x v‖ ^ 2) ∧
          m / (2 * (1 + L ^ 2)) ≤ truePhaseMargin (fun y ↦ F (p, y)) hFp x := by
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
  have hsource0 (p : P) :
      ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (fun x ↦ F0 (p, x)) := by
    simpa only [Function.comp_def] using
      hF0.comp (contMDiff_const.prodMk contMDiff_id :
        ContMDiff I (J.prod I) ∞ (fun x : M ↦ (p, x)))
  have hsource (p : P) :
      ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (fun x ↦ F (p, x)) := by
    simpa only [Function.comp_def] using
      hF.comp (contMDiff_const.prodMk contMDiff_id :
        ContMDiff I (J.prod I) ∞ (fun x : M ↦ (p, x)))
  have hD (p : P) (x : M) :
      (‖iteratedFDeriv ℝ 1 ((fun y ↦ F (p, y) - F0 (p, y)) ∘ (extChartAt I x).symm)
          (extChartAt I x x)‖ * ‖(tangentSpaceCastModel I x).toContinuousLinearMap‖ ≤ C1 * ε) ∧
      (actualHessianLiftConstant E (EuclideanSpace ℝ (Fin N)) *
          ‖iteratedFDeriv ℝ 2 ((fun y ↦ F (p, y) - F0 (p, y)) ∘ (extChartAt I x).symm)
            (extChartAt I x x)‖ * ‖(tangentSpaceCastModel I x).toContinuousLinearMap‖ ^ 2 ≤ C2 * ε) := by
    obtain ⟨O, T, U, hO, hTO, hU, hUT, hx, hsmooth, hnorm⟩ := hbudget (p, x)
    exact source_two_jet_bounds_of_joint_paperCoordinateC2 a (fun w ↦ F w - F0 w) p x
      hO hTO hU hUT hx hsmooth hε.le (hcast x) hnorm
  intro p
  refine ⟨hsource p, ?_⟩
  exact hstable (fun x ↦ F0 (p, x)) (fun x ↦ F (p, x)) (hsource0 p) (hsource p)
    (ξ p) (e p) (S p) (hA p) (hQ p)
    (fun x ↦ (hD p x).1.trans hC1ε) (fun x ↦ (hD p x).2.trans hC2ε)
    (hξ p) (hinv p) (hselector p) (hS p)

end ParametricPhase

#print axioms iteratedFDeriv_source_slice
#print axioms norm_iteratedFDeriv_source_slice_le
#print axioms source_chart_eq_joint_chart_slice
#print axioms source_chart_iteratedFDeriv_norm_le_joint
#print axioms source_chart_jet_le_of_joint_paperCoordinateCj
#print axioms source_two_jet_bounds_of_joint_paperCoordinateC2
#print axioms parametric_phase_regular_of_joint_paperCoordinateC2_budget

end GlobalEmbedding.Offline
