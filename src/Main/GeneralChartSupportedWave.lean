import Main.GeneralLegalWaveAbsorption
import Main.GeneralLegalWaveLocalDomains

/-!
# The exact coordinate-supported legal-wave entrance of the paper

`OpenSupportedLegalWave` is a useful stronger entrance for construction. The
paper additionally says that the smooth cutoff has compact support contained
in one coordinate chart. For nonempty support this record retains a chart
in the actual maximal smooth atlas. For empty support the mathematical empty
chart carries no data; Lean's total inverse of a partial homeomorphism must
not impose a spurious point of an empty source. No selected center or radial
cutoff is imposed. Its projection keeps the given cutoff, normal and phase.
-/

noncomputable section
open Set Function Manifold IsManifold
open scoped ContDiff Topology

namespace GlobalEmbedding.Continuation
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,E)

/-- Definition `defn:legal`: a smooth cutoff with compact support inside a
genuine smooth coordinate chart, with a smooth good phase and legal normal
on an open neighborhood of its support. The normal field may vanish. -/
structure ChartSupportedLegalWave
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    extends OpenSupportedLegalWave F hF where
  cutoff_compact : HasCompactSupport cutoff
  chart_support : (tsupport cutoff).Nonempty →
    ∃ chart : OpenPartialHomeomorph M E,
      chart ∈ maximalAtlas IM ∞ M ∧ tsupport cutoff ⊆ chart.source

namespace ChartSupportedLegalWave

variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin n))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}

/-- The previously used bump waves meet the exact paper entrance, without
any change to their leading value or tensor. -/
def ofLocal (w : LocalLegalWave (n := n) F hF) : ChartSupportedLegalWave (n := n) F hF := by
  exact {
    toOpenSupportedLegalWave := OpenSupportedLegalWave.ofLocal w
    cutoff_compact := w.cutoff.hasCompactSupport
    chart_support := fun _ => ⟨chartAt E w.center,
      chart_mem_maximalAtlas (I := IM) w.center,w.support_subset.trans w.domain_chart⟩ }

/-- A compactly supported local smooth cutoff on the given chart gives the
exact paper input. The existing local zero-extension proof supplies all
regularity, support, phase-covector and normal-fiber facts. -/
def ofLocalPresentation (w : LocallyPresentedLegalWave (n := n) F hF)
    (chart : OpenPartialHomeomorph M E) (hchart : chart ∈ maximalAtlas IM ∞ M)
    (hdomain : (w.domain : Set M) ⊆ chart.source) :
    ChartSupportedLegalWave (n := n) F hF := by
  exact {
    toOpenSupportedLegalWave := w.toOpenSupported
    cutoff_compact := w.cutoff_compact.extend_zero continuous_subtype_val
    chart_support := fun _ => ⟨chart,hchart,w.toOpenSupported.support_subset.trans hdomain⟩ }

/-- A nonempty cutoff support has a genuine common original coordinate
chart, with its actual maximal-atlas membership and support containment. -/
theorem exists_chart_of_support_nonempty (w : ChartSupportedLegalWave (n := n) F hF)
    (hne : (tsupport w.cutoff).Nonempty) :
    ∃ chart : OpenPartialHomeomorph M E,
      chart ∈ maximalAtlas IM ∞ M ∧ tsupport w.cutoff ⊆ chart.source :=
  w.chart_support hne

/-- On any nonempty source the guarded chart field recovers the literal
unconditional chart witness, even for a zero cutoff. Thus the guard changes
only the total-function encoding of the empty-manifold edge case. -/
theorem exists_chart [Nonempty M] (w : ChartSupportedLegalWave (n := n) F hF) :
    ∃ chart : OpenPartialHomeomorph M E,
      chart ∈ maximalAtlas IM ∞ M ∧ tsupport w.cutoff ⊆ chart.source := by
  classical
  by_cases hne : (tsupport w.cutoff).Nonempty
  · exact w.chart_support hne
  · let x : M := Classical.arbitrary M
    refine ⟨chartAt E x,chart_mem_maximalAtlas (I := IM) x,?_⟩
    intro y hy
    exact (hne ⟨y,hy⟩).elim

/-- An arbitrary legal open-supported wave on an empty source is retained;
no point is invented to supply the total inverse of a chart. -/
def ofIsEmpty [IsEmpty M] (w : OpenSupportedLegalWave (n := n) F hF) :
    ChartSupportedLegalWave (n := n) F hF := by
  have hempty : tsupport w.cutoff = (∅ : Set M) := by
    ext x
    exact isEmptyElim x
  exact {
    toOpenSupportedLegalWave := w
    cutoff_compact := by
      change IsCompact (tsupport w.cutoff)
      rw [hempty]
      exact isCompact_empty
    chart_support := fun h => isEmptyElim h.choose }

@[simp] theorem ofIsEmpty_projection [IsEmpty M]
    (w : OpenSupportedLegalWave (n := n) F hF) :
    (ofIsEmpty w).toOpenSupportedLegalWave = w := rfl

@[simp] theorem ofLocal_projection (w : LocalLegalWave (n := n) F hF) :
    (ofLocal w).toOpenSupportedLegalWave = OpenSupportedLegalWave.ofLocal w := rfl

@[simp] theorem ofLocalPresentation_projection (w : LocallyPresentedLegalWave (n := n) F hF)
    (chart : OpenPartialHomeomorph M E) (hchart : chart ∈ maximalAtlas IM ∞ M)
    (hdomain : (w.domain : Set M) ⊆ chart.source) :
    (ofLocalPresentation w chart hchart hdomain).toOpenSupportedLegalWave =
      w.toOpenSupported := rfl

end ChartSupportedLegalWave
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.ChartSupportedLegalWave.ofLocal
#print axioms GlobalEmbedding.Continuation.ChartSupportedLegalWave.ofLocalPresentation
#print axioms GlobalEmbedding.Continuation.ChartSupportedLegalWave.exists_chart_of_support_nonempty
#print axioms GlobalEmbedding.Continuation.ChartSupportedLegalWave.exists_chart
#print axioms GlobalEmbedding.Continuation.ChartSupportedLegalWave.ofIsEmpty

