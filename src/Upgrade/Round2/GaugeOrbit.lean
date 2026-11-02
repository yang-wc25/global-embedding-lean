import Upgrade.RankQSchurDifferential
import Upgrade.RankQSchurRank
import Upgrade.SupportedCoordinateTransport
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# The actual incidence equations annihilate target-coordinate orbit tangents

The Schur residual and the original supported defining equation are locally
zero on every invertible left translate of an incidence zero. Their native
Fréchet derivatives therefore annihilate `A ∘ C`. This is a zero-locus fact;
it does not assert cancellation away from the actual incidence locus.
-/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace GlobalEmbedding.Upgrade
open Paper

section OrbitDerivative
variable {S W R : Type*}
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup R] [NormedSpace ℝ R]

/-- Differentiating actual local constancy under left target transformations.
This lemma does not assume an incidence rank. -/
theorem fderiv_annihilates_target_orbit
    (C : S →L[ℝ] W) (equation : (S →L[ℝ] W) → R)
    (hR : DifferentiableAt ℝ equation C)
    (horbit : ∀ᶠ T : W →L[ℝ] W in 𝓝 (ContinuousLinearMap.id ℝ W),
      equation (T.comp C) = 0)
    (A : W →L[ℝ] W) :
    fderiv ℝ equation C (A.comp C) = 0 := by
  let P : (W →L[ℝ] W) →L[ℝ] (S →L[ℝ] W) :=
    (ContinuousLinearMap.compL ℝ S W W).flip C
  have hP : P (ContinuousLinearMap.id ℝ W) = C := by
    ext v
    rfl
  have hc := hR.hasFDerivAt.comp (ContinuousLinearMap.id ℝ W)
    P.hasFDerivAt
  have hz : HasFDerivAt (fun T : W →L[ℝ] W ↦ equation (T.comp C))
      (0 : (W →L[ℝ] W) →L[ℝ] R) (ContinuousLinearMap.id ℝ W) :=
    (hasFDerivAt_const (0 : R) (ContinuousLinearMap.id ℝ W)).congr_of_eventuallyEq horbit
  have hcomp : (fderiv ℝ equation C).comp P = 0 := hc.unique hz
  exact DFunLike.congr_fun hcomp A

end OrbitDerivative

section Schur
variable {S W : Type*}
  [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

private theorem gauge_rank_left_injective (C : S →L[ℝ] W)
    (T : W →L[ℝ] W) (hT : Function.Injective T) :
    Module.finrank ℝ (T.comp C).range = Module.finrank ℝ C.range := by
  have hk : (T.comp C).ker = C.ker := by
    ext v
    change T (C v) = 0 ↔ C v = 0
    exact ⟨fun h ↦ hT (h.trans T.map_zero.symm), fun h ↦ by rw [h, map_zero]⟩
  have h₁ := (T.comp C).toLinearMap.finrank_range_add_finrank_ker
  have h₂ := C.toLinearMap.finrank_range_add_finrank_ker
  change Module.finrank ℝ (T.comp C).range + Module.finrank ℝ (T.comp C).ker = _ at h₁
  rw [hk] at h₁
  omega

/-- At every actual Schur zero in the same fixed invertible-block chart,
all infinitesimal changes of target coordinates are killed exactly. -/
theorem rankQSchur_fderiv_target_orbit_zero (B C : S →L[ℝ] W)
    (hA : (rankQBlockA B C).IsInvertible) (hzero : rankQSchur B C = 0)
    (A : W →L[ℝ] W) :
    fderiv ℝ (rankQSchur B) C (A.comp C) = 0 := by
  apply fderiv_annihilates_target_orbit C (rankQSchur B)
    ((rankQSchur_contDiffAt B C hA).differentiableAt (by simp)) ?_ A
  have hid : (ContinuousLinearMap.id ℝ W).IsInvertible :=
    ⟨ContinuousLinearEquiv.refl ℝ W, rfl⟩
  have htrans : Continuous (fun T : W →L[ℝ] W ↦ T.comp C) :=
    continuous_id.clm_comp continuous_const
  have hId : (ContinuousLinearMap.id ℝ W).comp C = C := by ext v; rfl
  have hblock : ∀ᶠ T : W →L[ℝ] W in 𝓝 (ContinuousLinearMap.id ℝ W),
      (rankQBlockA B (T.comp C)).IsInvertible := by
    have ht : Tendsto (fun T : W →L[ℝ] W ↦ T.comp C)
        (𝓝 (ContinuousLinearMap.id ℝ W)) (𝓝 C) := by
      simpa only [ContinuousAt, hId] using! htrans.continuousAt
    exact ht.eventually ((rankQBlockA_contDiff B).continuous.continuousAt.preimage_mem_nhds
      hA.eventually_nhds)
  filter_upwards [hid.eventually_nhds, hblock] with T hT hTC
  apply (rankQSchur_eq_zero_iff_rank B (T.comp C) hTC).2
  rw [gauge_rank_left_injective C T hT.bijective.1]
  exact (rankQSchur_eq_zero_iff_rank B C hA).1 hzero

end Schur

section Supported
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed
variable {E W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- The SAME local defining equation supplied by accepted supported-rank
annihilates every target-GL orbit tangent at every supported incidence zero
in its open domain. Its codimension and rank proof are unchanged. -/
theorem supportedEquation_fderiv_target_orbit_zero
    {ambient : Set (SymmetricSquare E →L[ℝ] W)}
    {B C : SymmetricSquare E →L[ℝ] W}
    (chart : SupportedLocusLocalEquations ambient
      {D : SymmetricSquare E →L[ℝ] W | HasSupportedKernel D.toLinearMap} B)
    (hdom : C ∈ chart.domain) (hzero : chart.equation C = 0)
    (A : W →L[ℝ] W) :
    fderiv ℝ chart.equation C (A.comp C) = 0 := by
  apply fderiv_annihilates_target_orbit C chart.equation
    ((chart.contDiffOn_equation.contDiffAt
      (chart.isOpen_domain.mem_nhds hdom)).differentiableAt (by simp)) ?_ A
  have hid : (ContinuousLinearMap.id ℝ W).IsInvertible :=
    ⟨ContinuousLinearEquiv.refl ℝ W, rfl⟩
  have htrans : Continuous (fun T : W →L[ℝ] W ↦ T.comp C) :=
    continuous_id.clm_comp continuous_const
  have hId : (ContinuousLinearMap.id ℝ W).comp C = C := by ext v; rfl
  have ht : Tendsto (fun T : W →L[ℝ] W ↦ T.comp C)
      (𝓝 (ContinuousLinearMap.id ℝ W)) (𝓝 C) := by
    simpa only [ContinuousAt, hId] using! htrans.continuousAt
  have hsupport : HasSupportedKernel C.toLinearMap :=
    (chart.mem_locus_iff C hdom).2 hzero
  filter_upwards [hid.eventually_nhds, ht.eventually (chart.isOpen_domain.mem_nhds hdom)]
    with T hT hTC
  apply (chart.mem_locus_iff (T.comp C) hTC).1
  exact (hasSupportedKernel_postcomp_iff C.toLinearMap T.toLinearMap hT.bijective.1).2 hsupport

end Supported

#print axioms fderiv_annihilates_target_orbit
#print axioms rankQSchur_fderiv_target_orbit_zero
#print axioms supportedEquation_fderiv_target_orbit_zero

end GlobalEmbedding.Upgrade
