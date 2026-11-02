import GlobalEmbedding.Offline.FiniteSeparatedNet
import GlobalEmbedding.Offline.RiemannianFiniteNet
import GlobalEmbedding.Offline.VolumePacking
import GlobalEmbedding.Paper.InitializationColoredCutoffsColoring

/-!
# A separated net with the actual bounded enlarged-ball coloring

Source: main.tex, `prop:initialization`, lines 801–803. This connects the
proved exact-radius net and volume-packing estimate to the ORIGINAL greedy
coloring theorem. The actual palette has `ceil ((β/α)*30^n) + 2` colors,
independent of the scale and the cardinality of the net.

Uniform Riemannian volume comparison remains an explicit input provider.
No bound on the number of vertices is assumed or inserted into the palette.
-/

open Set Metric MeasureTheory Manifold Bundle
open scoped ENNReal ContDiff Manifold

noncomputable section

namespace GlobalEmbedding.Offline

section EMetric

variable {X : Type*} [PseudoEMetricSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X]

/-- The actual enlarged-ball graph has an actual proper coloring with the
source's fixed palette, by the previously proved native graph-coloring theorem. -/
theorem scaled_closedBallIntersectionGraph_colorable
    {ι : Type*} [Fintype ι] (c : ι → X) (μ : Measure X)
    (n : ℕ) {ρ K α β : ℝ} (hρ : 0 < ρ) (hK : 1 ≤ K)
    (hα : 0 < α) (hβ : 0 ≤ β)
    (hsep : ∀ i j, i ≠ j → ENNReal.ofReal (ρ / (10 * K)) ≤ edist (c i) (c j))
    (hvolume : ∀ x : X, ∀ s : ℝ, 0 < s → s ≤ ρ →
      ENNReal.ofReal (α * s ^ n) ≤ μ (eball x (ENNReal.ofReal s)) ∧
      μ (eball x (ENNReal.ofReal s)) ≤ ENNReal.ofReal (β * s ^ n)) :
    Nonempty ((closedBallIntersectionGraph c (ENNReal.ofReal (ρ / (4 * K)))).Coloring
      (Fin (⌈(β / α) * (30 : ℝ) ^ n⌉₊ + 2))) := by
  classical
  apply initialization_colored_cutoffs_coloring
  intro i
  rw [← SimpleGraph.ncard_neighborSet]
  exact scaled_closedBallIntersectionGraph_degree_le c μ n hρ hK hα hβ hsep hvolume i

/-- Compactness and the given volume comparison produce the SAME finite
net, exact open cover, separation threshold, and actual enlarged-ball coloring.
This includes the empty space and infinitely separated components. -/
theorem exists_separated_colored_net [CompactSpace X]
    (μ : Measure X) (n : ℕ) {ρ K α β : ℝ}
    (hρ : 0 < ρ) (hK : 1 ≤ K) (hα : 0 < α) (hβ : 0 ≤ β)
    (hvolume : ∀ x : X, ∀ s : ℝ, 0 < s → s ≤ ρ →
      ENNReal.ofReal (α * s ^ n) ≤ μ (eball x (ENNReal.ofReal s)) ∧
      μ (eball x (ENNReal.ofReal s)) ≤ ENNReal.ofReal (β * s ^ n)) :
    ∃ P : Set X, P.Finite ∧
      P.Pairwise (fun x y ↦ ENNReal.ofReal (ρ / (10 * K)) ≤ edist x y) ∧
      (∀ x : X, ∃ p ∈ P, edist x p < ENNReal.ofReal (ρ / (10 * K))) ∧
      Nonempty ((closedBallIntersectionGraph (Subtype.val : P → X)
        (ENNReal.ofReal (ρ / (4 * K)))).Coloring
          (Fin (⌈(β / α) * (30 : ℝ) ^ n⌉₊ + 2))) := by
  classical
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  obtain ⟨P, hfinite, hsep, hcover⟩ :=
    exists_compact_finite_separated_open_net (X := X)
      (ENNReal.ofReal_pos.mpr (by positivity : 0 < ρ / (10 * K)))
  let : Fintype P := hfinite.fintype
  refine ⟨P, hfinite, hsep, hcover, ?_⟩
  apply scaled_closedBallIntersectionGraph_colorable (Subtype.val : P → X) μ n
    hρ hK hα hβ (hvolume := hvolume)
  intro p q hpq
  exact hsep p.property q.property (fun heq ↦ hpq (Subtype.ext heq))

end EMetric

section Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsManifold I 1 M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [RegularSpace M] [CompactSpace M] [MeasurableSpace M] [OpensMeasurableSpace M]

/-- Actual Riemannian specialization, retaining same-component covering.
The graph uses the actual Riemannian extended distance, whose topology is
definitionally the original one under Mathlib's constructor. The supplied
measure may therefore be the same original Riemannian volume measure. -/
theorem exists_riemannian_separated_colored_net
    (μ : Measure M) (n : ℕ) {ρ K α β : ℝ}
    (hρ : 0 < ρ) (hK : 1 ≤ K) (hα : 0 < α) (hβ : 0 ≤ β)
    (hvolume : ∀ x : M, ∀ s : ℝ, 0 < s → s ≤ ρ →
      ENNReal.ofReal (α * s ^ n) ≤
        μ {y | riemannianEDist I y x < ENNReal.ofReal s} ∧
      μ {y | riemannianEDist I y x < ENNReal.ofReal s} ≤ ENNReal.ofReal (β * s ^ n)) :
    letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
    ∃ P : Set M, P.Finite ∧
      P.Pairwise (fun x y ↦ ENNReal.ofReal (ρ / (10 * K)) ≤ riemannianEDist I x y) ∧
      (∀ x : M, ∃ p ∈ P, p ∈ connectedComponent x ∧
        riemannianEDist I x p < ENNReal.ofReal (ρ / (10 * K))) ∧
      Nonempty ((closedBallIntersectionGraph (Subtype.val : P → M)
        (ENNReal.ofReal (ρ / (4 * K)))).Coloring
          (Fin (⌈(β / α) * (30 : ℝ) ^ n⌉₊ + 2))) := by
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  obtain ⟨P, hfinite, hsep, hcover, hcolor⟩ :=
    exists_separated_colored_net μ n hρ hK hα hβ hvolume
  refine ⟨P, hfinite, hsep, ?_, hcolor⟩
  intro x
  obtain ⟨p, hp, hdist⟩ := hcover x
  exact ⟨p, hp, pathComponent_subset_component x
    (joined_of_riemannianEDist_lt hdist), hdist⟩

end Riemannian

#print axioms scaled_closedBallIntersectionGraph_colorable
#print axioms exists_separated_colored_net
#print axioms exists_riemannian_separated_colored_net

end GlobalEmbedding.Offline
