import GlobalEmbedding.Offline.FiniteSeparatedNet
import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# Finite separated open nets for the actual Riemannian distance

Source: `prop:initialization`, main.tex line 801; DAG leaf
`initialization-colored-cutoffs-separated-net-finite-maximal-net`.

The metric is Mathlib's actual `Manifold.riemannianEDist`, constructed from
lengths of smooth paths in the given Riemannian tangent bundle. Its topology
agrees with the original manifold topology. A finite covering distance
also supplies a path, so each chosen center is in the same connected
component as the covered point. Empty and disconnected manifolds are allowed.
-/

open Set Manifold Bundle
open scoped Manifold ContDiff ENNReal

noncomputable section

namespace GlobalEmbedding.Offline

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Finite Riemannian distance cannot join different path components.
This follows directly from the infimum over genuine smooth paths, without
assuming that the manifold is connected or that all distances are finite. -/
theorem joined_of_riemannianEDist_lt [∀ x : M, ENorm (TangentSpace I x)]
    {x y : M} {δ : ℝ≥0∞} (h : riemannianEDist I x y < δ) : Joined x y := by
  change Nonempty (Path x y)
  by_contra hn
  let : IsEmpty (Path x y) := not_nonempty_iff.mp hn
  have htop : riemannianEDist I x y = ⊤ := by simp [riemannianEDist]
  rw [htop] at h
  exact not_top_lt h

/-- The exact-radius net for an actual continuous Riemannian tangent metric.
Separation is required even across components, where the extended distance
may be infinite. Covering is strict and always stays in the component. -/
theorem exists_riemannian_finite_separated_open_net
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsManifold I 1 M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [RegularSpace M] [CompactSpace M]
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ P : Set M, P.Finite ∧
      P.Pairwise (fun x y ↦ δ ≤ riemannianEDist I x y) ∧
      ∀ x : M, ∃ p ∈ P, p ∈ connectedComponent x ∧ riemannianEDist I x p < δ := by
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  obtain ⟨P, hfinite, hsep, hcover⟩ :=
    exists_compact_finite_separated_open_net (X := M) hδ
  refine ⟨P, hfinite, hsep, ?_⟩
  intro x
  obtain ⟨p, hp, hxp⟩ := hcover x
  exact ⟨p, hp, pathComponent_subset_component x (joined_of_riemannianEDist_lt hxp), hxp⟩

/-- The exact initialization leaf, for the native smooth Riemannian metric
already used in the repository. Compactness and Hausdorffness provide the
regular topology required by the distance construction. The radius is the
given positive real number, with no change of scale and no connectedness or
nonemptiness assumption. In fact, finite dimensionality is unnecessary here. -/
theorem exists_smooth_riemannian_finite_separated_open_net
    [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I (M := M)))
    {δ : ℝ} (hδ : 0 < δ) :
    letI : RiemannianBundle (TangentSpace I (M := M)) := ⟨g.toRiemannianMetric⟩
    ∃ P : Set M, P.Finite ∧
      P.Pairwise (fun x y ↦ ENNReal.ofReal δ ≤ riemannianEDist I x y) ∧
      ∀ x : M, ∃ p ∈ P, p ∈ connectedComponent x ∧
        riemannianEDist I x p < ENNReal.ofReal δ := by
  let : RiemannianBundle (TangentSpace I (M := M)) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I (M := M)) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  exact exists_riemannian_finite_separated_open_net (ENNReal.ofReal_pos.mpr hδ)

#print axioms joined_of_riemannianEDist_lt
#print axioms exists_riemannian_finite_separated_open_net
#print axioms exists_smooth_riemannian_finite_separated_open_net

end GlobalEmbedding.Offline
