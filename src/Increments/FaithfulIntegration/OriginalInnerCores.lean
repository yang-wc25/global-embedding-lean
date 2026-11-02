import FaithfulRepair.OriginalCompactFamily
import FaithfulRepair.OriginalMapFiniteness

/-!
# Compact host cores inside the given source inners

The original source inners already form an open cover.  Restricting an
internal host chart to its inner does not change either coordinate function.
It ensures that the reverse source transition is evaluated in the host's
ORIGINAL Omega, by the original source_inner_norm field.  No open Q, compact
Omega, global parameter cover or extra inverse-frame budget is assumed.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation.FaithfulIntegration
open FaithfulRepair

variable {n d N q : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  [R1Space M] [R1Space P]

/-- The host coframe's observation point is forced into its own original
source norm domain by geometry already present in the original record. -/
theorem original_inner_compact_family_jet_cores
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D)
    (C W : Set (P × M)) (hC : IsCompact C) (hW : IsOpen W) (hCW : C ⊆ W)
    (hCK : C ⊆ D.parameterSet ×ˢ (univ : Set M))
    (f : (Fin D.atlas.count × Fin D.parameterCount) → (Fin (n+d) → ℝ) → Fin q → ℝ)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i)
      ((originalJointCoordinateChart D i).target ∩ (originalJointCoordinateChart D i).symm ⁻¹' W)) :
    ∃ core : (Fin D.atlas.count × Fin D.parameterCount) → Set (P × M),
      (∀ i, IsCompact (core i)) ∧
      (∀ i, core i ⊆ (originalJointCoordinateChart D i).source ∩ W) ∧
      (∀ i z, z ∈ core i → z.2 ∈ D.atlas.inner i.1) ∧
      C = ⋃ i, core i ∧
      ∀ j : ℕ, ∃ R : ℝ, 0 ≤ R ∧ ∀ i k, k ≤ j →
        ∀ y ∈ (originalJointCoordinateChart D i) '' core i,
          ‖iteratedFDeriv ℝ k (f i) y‖ ≤ R := by
  let inner := fun i : Fin D.atlas.count × Fin D.parameterCount =>
    (univ : Set P) ×ˢ D.atlas.inner i.1
  have hInner : ∀ i, IsOpen (inner i) := fun i => isOpen_univ.prod (D.atlas.inner_open i.1)
  let chart := fun i => (originalJointCoordinateChart D i).restrOpen (inner i) (hInner i)
  have hChartSource : ∀ i, (chart i).source = (originalJointCoordinateChart D i).source ∩ inner i :=
    fun _ => rfl
  have hCover : ∀ z ∈ C, ∃ i, z ∈ (chart i).source := by
    intro z hz
    obtain ⟨p,hp,_⟩ := hd.parameter_cover z.1 (hCK hz).1
    obtain ⟨s,hs⟩ := D.atlas.cover z.2
    refine ⟨(s,p),?_⟩
    rw [hChartSource, originalJointCoordinateChart_source]
    exact ⟨⟨hp,D.atlas.inner_subset s hs⟩,mem_univ _,hs⟩
  have hf' : ∀ i, ContDiffOn ℝ ∞ (f i) ((chart i).target ∩ (chart i).symm ⁻¹' W) :=
    fun i => (hf i).mono (fun _ hy => ⟨hy.1.1,hy.2⟩)
  obtain ⟨core,hCompact,hSub,hCovered,hJets⟩ :=
    original_compact_family_jet_cores chart C W hC hW hCW hCover f hf'
  refine ⟨core,hCompact,?_,?_,hCovered,hJets⟩
  · intro i z hz
    have h := hSub i hz
    rw [hChartSource] at h
    exact ⟨h.1.1,h.2⟩
  · intro i z hz
    have h := hSub i hz
    rw [hChartSource] at h
    exact h.1.2.2

end GlobalEmbedding.Continuation.FaithfulIntegration

#print axioms GlobalEmbedding.Continuation.FaithfulIntegration.original_inner_compact_family_jet_cores

