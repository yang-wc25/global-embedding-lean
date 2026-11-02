import Upgrade.SupportedCoordinateTransport
import GlobalEmbedding.Paper.SmoothImmersionNormalProjection
import GlobalEmbedding.Paper.UpgradeLocalTrueFormCoefficients
import GlobalEmbedding.Paper.ImmersionNormalRank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Actual fixed normal coordinates for supported incidence

Source: the supported-locus steps of `thm:upgrade`. The normal target used by a
defining equation is the actual normal space at the selected base point. At
nearby points we restrict its original orthogonal projection to the actual
moving normal space. Smoothness of the original normal projection gives a
uniform lower bound for this restriction on a genuine open neighborhood.
No arbitrary normal frame, orientation, or supplied incidence rank occurs.
-/

noncomputable section
open Bundle Filter Manifold Set Module
open scoped ContDiff Topology

namespace GlobalEmbedding.Upgrade
open GlobalEmbedding.Paper
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

section Projection
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A literal fixed normal projection has a quantitative lower bound on a
nearby actual normal space. This estimates the actual coordinate operator,
not an independently supplied isomorphism. -/
theorem normal_coordinate_lower_bound
    (U W : Submodule ℝ V) [U.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (v : W) :
    (1 - ‖W.starProjection - U.starProjection‖) * ‖v‖ ≤
      ‖U.orthogonalProjectionOnto (v : V)‖ := by
  have heq : (W.starProjection - U.starProjection) (v : V) +
      U.starProjection (v : V) = (v : V) := by
    simp only [sub_apply, sub_add_cancel,
      W.starProjection_mem_subspace_eq_self]
  have htriangle := norm_add_le
    ((W.starProjection - U.starProjection) (v : V)) (U.starProjection (v : V))
  have hop := (W.starProjection - U.starProjection).le_opNorm (v : V)
  rw [heq] at htriangle
  have hnorm : ‖U.starProjection (v : V)‖ =
      ‖U.orthogonalProjectionOnto (v : V)‖ := rfl
  rw [hnorm] at htriangle
  change (1 - ‖W.starProjection - U.starProjection‖) * ‖(v : V)‖ ≤ _
  nlinarith

/-- Projection gap less than one makes the actual normal coordinate map
injective. Only this injectivity is needed for the original supported kernel
to agree with the supported kernel in fixed normal coordinates. -/
theorem normal_coordinate_injective
    (U W : Submodule ℝ V) [U.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hgap : ‖W.starProjection - U.starProjection‖ < 1) :
    Function.Injective (U.orthogonalProjectionOnto.comp W.subtypeL) := by
  intro v w h
  have hzero : U.orthogonalProjectionOnto ((v - w : W) : V) = 0 := by
    rw [Submodule.coe_sub, map_sub]
    exact sub_eq_zero.mpr h
  have hlower := normal_coordinate_lower_bound U W (v - w)
  rw [hzero, norm_zero] at hlower
  have hvw : ‖v - w‖ = 0 := by
    have hpos : 0 < 1 - ‖W.starProjection - U.starProjection‖ := by linarith
    nlinarith [norm_nonneg (v - w)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hvw)

end Projection

section Manifold
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {N : ℕ}

/-- The fixed target is the original normal space at the actual base point. -/
def fixedNormalCoordinate
    (F : M → EuclideanSpace ℝ (Fin N)) (x z : M) :
    normalSpace (I := I) F z →L[ℝ] normalSpace (I := I) F x :=
  (normalSpace (I := I) F x).orthogonalProjectionOnto.comp
    (normalSpace (I := I) F z).subtypeL

omit [IsManifold I ∞ M] [BoundarylessManifold I M] in
/-- The actual normal coordinate map is bijective: injectivity comes from
the quantitative projection gap, and surjectivity from the actual constant
normal dimension of the original immersion. No normal equivalence is input. -/
theorem fixedNormalCoordinate_bijective
    (F : M → EuclideanSpace ℝ (Fin N))
    (himm : ∀ z, Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F z))
    (x z : M)
    (hgap : ‖(normalSpace (I := I) F z).starProjection -
      (normalSpace (I := I) F x).starProjection‖ < 1) :
    Function.Bijective (fixedNormalCoordinate (I := I) F x z) := by
  have hinj : Function.Injective (fixedNormalCoordinate (I := I) F x z) :=
    normal_coordinate_injective _ _ hgap
  have hdim : finrank ℝ (normalSpace (I := I) F z) =
      finrank ℝ (normalSpace (I := I) F x) := by
    rw [immersion_normal_rank F z (himm z), immersion_normal_rank F x (himm x)]
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩

/-- The proved actual fixed normal coordinate equivalence. It is constructed
from the original orthogonal projection, rather than supplied as a frame. -/
def fixedNormalCoordinateEquiv
    (F : M → EuclideanSpace ℝ (Fin N))
    (himm : ∀ z, Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F z))
    (x z : M)
    (hgap : ‖(normalSpace (I := I) F z).starProjection -
      (normalSpace (I := I) F x).starProjection‖ < 1) :
    normalSpace (I := I) F z ≃L[ℝ] normalSpace (I := I) F x :=
  (LinearEquiv.ofBijective (fixedNormalCoordinate (I := I) F x z).toLinearMap
    (fixedNormalCoordinate_bijective F himm x z hgap)).toContinuousLinearEquiv

theorem fixedNormalCoordinateEquiv_toContinuousLinearMap
    (F : M → EuclideanSpace ℝ (Fin N))
    (himm : ∀ z, Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F z))
    (x z : M)
    (hgap : ‖(normalSpace (I := I) F z).starProjection -
      (normalSpace (I := I) F x).starProjection‖ < 1) :
    (fixedNormalCoordinateEquiv F himm x z hgap).toContinuousLinearMap =
      fixedNormalCoordinate (I := I) F x z := by
  apply ContinuousLinearMap.ext
  intro v
  rfl

/-- The same actual normal chart has an inverse norm bound on the one-half
projection neighborhood. This is a quantitative margin usable by Schur data. -/
theorem fixedNormalCoordinateEquiv_symm_norm_le_two
    (F : M → EuclideanSpace ℝ (Fin N))
    (himm : ∀ z, Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F z))
    (x z : M)
    (hgap : ‖(normalSpace (I := I) F z).starProjection -
      (normalSpace (I := I) F x).starProjection‖ < (1 / 2 : ℝ))
    (v : normalSpace (I := I) F x) :
    ‖(fixedNormalCoordinateEquiv F himm x z (hgap.trans (by norm_num))).symm v‖ ≤
      2 * ‖v‖ := by
  let e := fixedNormalCoordinateEquiv F himm x z (hgap.trans (by norm_num))
  have h := normal_coordinate_lower_bound (normalSpace (I := I) F x)
    (normalSpace (I := I) F z) (e.symm v)
  have he : (normalSpace (I := I) F x).orthogonalProjectionOnto
      (e.symm v : EuclideanSpace ℝ (Fin N)) = v := e.apply_symm_apply v
  rw [he] at h
  change ‖e.symm v‖ ≤ 2 * ‖v‖
  nlinarith [norm_nonneg (e.symm v)]

/-- An actual smooth immersion supplies a genuine open neighborhood on which
the fixed normal coordinate map is injective and has a uniform one-half lower
bound. This retains disconnected manifolds and uses no choice of orientation. -/
theorem exists_fixed_normal_coordinate_neighborhood
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (himm : ∀ z, Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F z))
    (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ U ⊆ (chartAt H x).source ∧
      ∀ z ∈ U,
        ‖(normalSpace (I := I) F z).starProjection -
          (normalSpace (I := I) F x).starProjection‖ < (1 / 2 : ℝ) ∧
        Function.Injective (fixedNormalCoordinate (I := I) F x z) ∧
        ∀ v : normalSpace (I := I) F z,
          (1 / 2 : ℝ) * ‖v‖ ≤ ‖fixedNormalCoordinate (I := I) F x z v‖ := by
  have hp := (smooth_immersion_normal_projection F hF himm).continuous
  let U : Set M := (chartAt H x).source ∩
    {z | ‖(normalSpace (I := I) F z).starProjection -
      (normalSpace (I := I) F x).starProjection‖ < (1 / 2 : ℝ)}
  have hU : IsOpen U := (chartAt H x).open_source.inter
    (isOpen_lt (hp.sub continuous_const).norm continuous_const)
  refine ⟨U, hU, ?_, inter_subset_left, ?_⟩
  · exact ⟨mem_chart_source H x, by simp⟩
  · intro z hz
    have hgap := hz.2
    change ‖(normalSpace (I := I) F z).starProjection -
      (normalSpace (I := I) F x).starProjection‖ < (1 / 2 : ℝ) at hgap
    refine ⟨hgap, normal_coordinate_injective _ _ (hgap.trans (by norm_num)), ?_⟩
    intro v
    have h := normal_coordinate_lower_bound (normalSpace (I := I) F x)
      (normalSpace (I := I) F z) v
    change (1 / 2 : ℝ) * ‖v‖ ≤
      ‖(normalSpace (I := I) F x).orthogonalProjectionOnto (v : EuclideanSpace ℝ (Fin N))‖
    nlinarith [norm_nonneg v]

end Manifold

#print axioms normal_coordinate_lower_bound
#print axioms normal_coordinate_injective
#print axioms fixedNormalCoordinate
#print axioms fixedNormalCoordinate_bijective
#print axioms fixedNormalCoordinateEquiv
#print axioms fixedNormalCoordinateEquiv_toContinuousLinearMap
#print axioms fixedNormalCoordinateEquiv_symm_norm_le_two
#print axioms exists_fixed_normal_coordinate_neighborhood

end GlobalEmbedding.Upgrade
