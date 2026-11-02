import Initialization.Geometry.AmbientVolume
import GlobalEmbedding.Offline.FiniteSeparatedNet
import GlobalEmbedding.Offline.SeparatedNetColoring
import Mathlib.Geometry.Manifold.WhitneyEmbedding

/-!
# Actual fixed-palette nets from a compact smooth source

This alternate preparation for `prop:initialization` uses a fixed auxiliary
Whitney embedding solely to construct local cutoffs. The existing separated-net,
volume-packing and coloring proofs are reused verbatim, with their volume inputs
now discharged by actual Euclidean volume. The target dimension of H is unchanged.
No connectedness, nonemptiness or positive auxiliary dimension is assumed.
-/

open Set Metric MeasureTheory Manifold IsManifold Function Topology
open scoped ENNReal Manifold ContDiff

noncomputable section
namespace GlobalEmbedding.Initialization

/-- Every actual separated family in the auxiliary Euclidean space has the
fixed palette `30^d+2`. Its graph is the original enlarged-closed-ball graph.
The volume comparison is proved internally, not supplied as a hypothesis. -/
theorem euclidean_scaled_closedBall_colorable
    {d : ℕ} {ι : Type*} [Fintype ι]
    (c : ι → EuclideanSpace ℝ (Fin d)) {ρ K : ℝ}
    (hρ : 0 < ρ) (hK : 1 ≤ K)
    (hsep : ∀ i j, i ≠ j →
      ENNReal.ofReal (ρ / (10 * K)) ≤ edist (c i) (c j)) :
    Nonempty ((GlobalEmbedding.Offline.closedBallIntersectionGraph c
      (ENNReal.ofReal (ρ / (4 * K)))).Coloring (Fin (30 ^ d + 2))) := by
  obtain ⟨α, hα, hvolume⟩ := exists_euclidean_ball_volume_coefficient d
  have hcomparison (x : EuclideanSpace ℝ (Fin d)) (r : ℝ)
      (hr : 0 < r) (_hrρ : r ≤ ρ) :
      ENNReal.ofReal (α * r ^ d) ≤ volume (eball x (ENNReal.ofReal r)) ∧
      volume (eball x (ENNReal.ofReal r)) ≤ ENNReal.ofReal (α * r ^ d) :=
    ⟨(hvolume x r hr).symm.le, (hvolume x r hr).le⟩
  have h := GlobalEmbedding.Offline.scaled_closedBallIntersectionGraph_colorable
    c volume d hρ hK hα hα.le hsep hcomparison
  have hcast : (30 : ℝ) ^ d = ((30 ^ d : ℕ) : ℝ) := by norm_cast
  simpa only [div_self hα.ne', one_mul, hcast, Nat.ceil_natCast] using h

/-- A finite exact-radius net and actual enlarged-ball coloring for any compact
Euclidean subset. Constants are independent of its number of points and of K.
Unlike the earlier Riemannian-net consumer, this statement has no volume input. -/
theorem exists_compact_euclidean_colored_net
    {d : ℕ} {S : Set (EuclideanSpace ℝ (Fin d))} (hS : IsCompact S)
    {ρ K : ℝ} (hρ : 0 < ρ) (hK : 1 ≤ K) :
    ∃ P : Set (EuclideanSpace ℝ (Fin d)), P ⊆ S ∧ P.Finite ∧
      P.Pairwise (fun x y ↦ ENNReal.ofReal (ρ / (10 * K)) ≤ edist x y) ∧
      (∀ x ∈ S, ∃ p ∈ P, edist x p < ENNReal.ofReal (ρ / (10 * K))) ∧
      Nonempty ((GlobalEmbedding.Offline.closedBallIntersectionGraph
        (Subtype.val : P → EuclideanSpace ℝ (Fin d))
        (ENNReal.ofReal (ρ / (4 * K)))).Coloring (Fin (30 ^ d + 2))) := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  obtain ⟨P, hPS, hfinite, hsep, hcover⟩ :=
    GlobalEmbedding.Offline.exists_finite_weakly_separated_open_net hS.totallyBounded
      (ENNReal.ofReal_pos.mpr (by positivity : 0 < ρ / (10 * K)))
  letI : Fintype P := hfinite.fintype
  refine ⟨P, hPS, hfinite, hsep, hcover, ?_⟩
  apply euclidean_scaled_closedBall_colorable Subtype.val hρ hK
  intro i j hij
  exact hsep i.property j.property (fun h ↦ hij (Subtype.ext h))

/-- A compact smooth manifold supplies a single smooth auxiliary embedding,
and therefore all the actual finite separated colored nets used by the
construction. The embedding dimension and palette are fixed before ρ,K.
The embedding is constructed by Mathlib's native compact Whitney theorem.
Its dimension never replaces the desired dimension `s_n+1` of the selector. -/
theorem exists_smooth_ambient_colored_nets
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [CompactSpace M] :
    ∃ (d : ℕ) (e : M → EuclideanSpace ℝ (Fin d)),
      ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ e ∧ IsClosedEmbedding e ∧
      (∀ x : M, Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) e x)) ∧
      ∀ (ρ K : ℝ), 0 < ρ → 1 ≤ K →
      ∃ P : Set (EuclideanSpace ℝ (Fin d)), P ⊆ range e ∧ P.Finite ∧
        P.Pairwise (fun x y ↦ ENNReal.ofReal (ρ / (10 * K)) ≤ edist x y) ∧
        (∀ x : M, ∃ p ∈ P, edist (e x) p < ENNReal.ofReal (ρ / (10 * K))) ∧
        Nonempty ((GlobalEmbedding.Offline.closedBallIntersectionGraph
          (Subtype.val : P → EuclideanSpace ℝ (Fin d))
          (ENNReal.ofReal (ρ / (4 * K)))).Coloring (Fin (30 ^ d + 2))) := by
  obtain ⟨d, e, he, hemb, himm⟩ := exists_embedding_euclidean_of_compact (I := I) (M := M)
  refine ⟨d, e, he, hemb, himm, ?_⟩
  intro ρ K hρ hK
  have hcompact : IsCompact (range e) := isCompact_range he.continuous
  obtain ⟨P, hPS, hfin, hsep, hcover, hcol⟩ :=
    exists_compact_euclidean_colored_net hcompact hρ hK
  exact ⟨P, hPS, hfin, hsep, fun x ↦ hcover (e x) ⟨x, rfl⟩, hcol⟩

end GlobalEmbedding.Initialization
