import NormalPolar.IdentificationTransportProbe
import NormalPolar.MapFamily
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The original total normal identification already implies total immersion

For two maps from the same source into the same Euclidean ambient space,
an isometry equivalence of their actual normal spaces forces their actual
differential ranges to have the same rank. If the reference differential is
injective, so is the new one. Thus an existing ProbeGeometry supplies the
global immersion needed for canonical polar reselection, even outside its
admitted metric domain.
-/

noncomputable section
open Manifold
open scoped ContDiff

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade

/-- Normal rank determines differential rank for the actual native maps.
This statement does not assume a metric equality outside an admitted domain. -/
theorem immersion_of_actual_normal_equiv
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] {N : ℕ}
    (F₀ F : M → EuclideanSpace ℝ (Fin N)) (x : M)
    (hi₀ : Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F₀ x))
    (Q : normalSpace (I := I) F x ≃ₗᵢ[ℝ] normalSpace (I := I) F₀ x) :
    Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F x) := by
  let cast₀ := tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (F₀ x)
  let cast := tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (F x)
  let D₀ := cast₀.toContinuousLinearMap.comp
    (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F₀ x)
  let D := cast.toContinuousLinearMap.comp
    (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F x)
  have hD₀ : Function.Injective D₀ := cast₀.injective.comp hi₀
  have hnormal : Module.finrank ℝ (normalSpace (I := I) F x) =
      Module.finrank ℝ (normalSpace (I := I) F₀ x) := Q.toLinearEquiv.finrank_eq
  have hsum₀ := (LinearMap.range D₀.toLinearMap).finrank_add_finrank_orthogonal
  have hsum := (LinearMap.range D.toLinearMap).finrank_add_finrank_orthogonal
  change Module.finrank ℝ (LinearMap.range D₀.toLinearMap) +
    Module.finrank ℝ (normalSpace (I := I) F₀ x) = _ at hsum₀
  change Module.finrank ℝ (LinearMap.range D.toLinearMap) +
    Module.finrank ℝ (normalSpace (I := I) F x) = _ at hsum
  have hrange : Module.finrank ℝ (LinearMap.range D.toLinearMap) =
      Module.finrank ℝ (TangentSpace I x) := by
    rw [hnormal] at hsum
    have h := LinearMap.finrank_range_of_inj hD₀
    omega
  have hnull := D.toLinearMap.finrank_range_add_finrank_ker
  have hker : Module.finrank ℝ (LinearMap.ker D.toLinearMap) = 0 := by omega
  have hD : Function.Injective D :=
    LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hker)
  intro a b hab
  apply hD
  change cast (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F x a) =
    cast (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F x b)
  rw [hab]

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The actual original total identification forces immersion of every
slice, not only the slices where the metric equality is required. -/
theorem probeGeometry_all_slice_immersion
    {F₀ : M → V} {r : ℕ} (g : ProbeGeometry (n := n) F₀ r)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x)) :
    ∀ t u x, Function.Injective (mfderiv IM 𝓘(ℝ, V) (g.map t u) x) := by
  intro t u x
  exact immersion_of_actual_normal_equiv F₀ (g.map t u) x (hi₀ x)
    (g.normalIdentification t u x)

/-- Canonical polar reselection for the same existing geometry. Global
immersion is derived from its existing total normal identification; no new
domain or domain-outside map extension is chosen. The response must still
be transported by the preceding actual-geometry theorems. -/
def canonicalProbeGeometryOfProbeGeometry
    {F₀ : M → V} {r : ℕ} (g : ProbeGeometry (n := n) F₀ r)
    (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (hreserve : ∀ t, 0 < t → t < g.threshold → ∀ u, ‖u‖ < g.radius → ∀ x,
      ‖(normalSpace (I := IM) F₀ x).starProjection -
        (normalSpace (I := IM) (g.map t u) x).starProjection‖ < 1) :
    ProbeGeometry (n := n) F₀ r :=
  probeGeometryOfActualImmersions F₀ hF₀ hi₀ g.map g.radius g.threshold
    g.radius_pos g.threshold_pos g.slice_smooth (probeGeometry_all_slice_immersion g hi₀)
    g.joint_smooth g.metric hreserve

end GlobalEmbedding.NormalPolar
