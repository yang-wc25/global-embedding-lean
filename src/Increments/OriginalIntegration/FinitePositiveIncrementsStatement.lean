import GlobalEmbedding.Paper.IncrementsOriginalQualitativeAdmissibility

/-!
# Literal fixed-decomposition conclusion of finite positive increments

This statement layer imports only original data and coordinate definitions.
It does not import an increment solver, prepared packet, or implementation
output predicate. The original map, target, chart norm domains, parameter
sample and cutoff labels appear literally. One U precedes every observation
order. The estimates are extended-real inequalities and therefore include
finiteness without relying on toReal at infinity.

This is the fixed-data existence part of lem:increments. It does not by
itself state common quantitative control across a varying class of maps or
phases, nor identify qualitative goodness with a fixed inverse margin.
-/

noncomputable section
open Set Function Manifold
open scoped ContDiff Topology ENNReal BigOperators
namespace GlobalEmbedding.Paper

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)

/-- Original primary supports and the pair intersections of the signed
quadratic terms, with only the internal refinement indices hidden. -/
def FinitePositiveIncrementSupport
    (Data : IncrementsOriginalNativeData n d N M P)
    (G : Set (P × M)) (U : P × M → Ey) : Prop :=
  ∃ (primary : Fin Data.primaryCount → P × M → Ey)
    (secondary : ((Fin Data.primaryCount × Fin Data.primaryCount) × Fin 4) → P × M → Ey),
    U = (fun z => (∑ nu, primary nu z) +
      ∑ r ∈ Finset.univ.filter (fun r : (Fin Data.primaryCount × Fin Data.primaryCount) × Fin 4 =>
        r.1.1 ≠ r.1.2 ∨ r.2 = 0 ∨ r.2 = 3), secondary r z) ∧
    (∀ nu, tsupport (fun z : G => primary nu z.val) ⊆
      Subtype.val ⁻¹' tsupport (Data.cutoff nu)) ∧
    (∀ r, tsupport (fun z : G => secondary r z.val) ⊆
      Subtype.val ⁻¹' (tsupport (Data.cutoff r.1.1) ∩ tsupport (Data.cutoff r.1.2))) ∧
    tsupport (fun z : G => U z.val) ⊆ Subtype.val ⁻¹' (⋃ nu, tsupport (Data.cutoff nu))

/-- The same real displacement satisfies both literal original estimates
at every order, on an open neighborhood of the original parameter sample. -/
def FinitePositiveIncrementAtScale
    (Data : IncrementsOriginalNativeData n d N M P)
    (q : ℕ) (C : ℕ → ℝ) (ell tau delta : ℝ) : Prop :=
  ∃ (G : Set (P × M)) (U : P × M → Ey), IsOpen G ∧
    Data.parameterSet ×ˢ (univ : Set M) ⊆ G ∧
    G ⊆ Data.parameterOpen ×ˢ (univ : Set M) ∧
    ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓘(ℝ,Es)) 𝓘(ℝ,Ey) ∞ U G ∧
    FinitePositiveIncrementSupport Data G U ∧
    ∀ j, paperAtlasWeighted 0 j tau
      (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart U)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet) ≤ ENNReal.ofReal (C j*delta*tau) ∧
      paperAtlasWeighted 0 j tau
        (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart
          (incrementsOriginalMetricError Data.F U Data.H delta))
        (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
        (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
          Data.parameterNormDomain Data.parameterSet) ≤
        ENNReal.ofReal (C j*(delta*(tau/ell)^q+delta^3/tau))

/-- The source's fixed actual decomposition exists at all permitted small
scales. The threshold and the sequence C precede scales and observation
orders; the same U works at every observation order. -/
def FinitePositiveIncrementsFixedData
    (Data : IncrementsOriginalNativeData n d N M P) : Prop :=
  ∀ q : ℕ, 1 ≤ q → ∃ Theta : ℝ, 0 < Theta ∧ Theta ≤ 1 ∧
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ ell, 0 < ell → ell ≤ 1 →
      ∀ tau delta, 0 < delta → delta ≤ tau → tau ≤ ell → tau/ell < Theta →
        FinitePositiveIncrementAtScale Data q C ell tau delta

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.FinitePositiveIncrementAtScale
#print axioms GlobalEmbedding.Paper.FinitePositiveIncrementsFixedData
