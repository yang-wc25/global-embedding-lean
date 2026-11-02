import Repair.ReferenceOriginalLocalFactory
import Repair.SourceCollarNovSquareSupport

/-!
The old numerical budget is retained verbatim.  Its existing finite
refinement producer, instantiated on a constant allowed field, supplies
centers and square cutoffs before the actual nonconvex source domain is
used.  Actual local geometry will then be constructed on the original
buffer ball at every chosen center.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Metric
open scoped ContDiff Topology TensorProduct BigOperators NNReal
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance novGeometryRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance novGeometrySquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {m d N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Edge" => EdgePair (Module.finrank ℝ D+1)
private local instance novGeometryTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) := inferInstance
private local instance novGeometryTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) := inferInstance

/-- Enlargement only changes the proof that the same chart source lies
inside the ambient domain. The chart map, inverse, source, target, radii,
and all estimates are definitionally unchanged. -/
def sourceCollarNov_lift_chart
    (b : RepairReferenceFactoryBudget m d N)
    {f : X → (SymmetricSquare D →L[ℝ] V) × (D →L[ℝ] D →L[ℝ] ℝ)}
    {U O : Set X} {x : X} {i : b.cover.indices} {a : Edge}
    (block : Round4UniformTemplateChart b.templateDim b.operatorBound b.phaseMargin b.tensorLower
      b.nativeTensor1 b.phaseMargin_pos b.tensorLower_pos f U x b.radius i a)
    (hUO : U ⊆ O) :
    Round4UniformTemplateChart b.templateDim b.operatorBound b.phaseMargin b.tensorLower
      b.nativeTensor1 b.phaseMargin_pos b.tensorLower_pos f O x b.radius i a :=
  { block with source_domain := block.source_domain.trans hUO }

/-- The exact existing per-host piece bound and cutoff profile are obtained
from the existing producer. No new number of charts enters either bound. -/
theorem sourceCollarNov_budget_refinement
    (b : RepairReferenceFactoryBudget m d N)
    (u : (SymmetricSquare D →L[ℝ] V) × (D →L[ℝ] D →L[ℝ] ℝ))
    (hu : u ∈ actualAllowedPhaseTensorData D V b.operatorBound b.phaseMargin b.tensorLower b.nativeTensor1)
    (K : Set X) (center : X) (hKball : K ⊆ closedBall center b.modelRadius) :
    ∃ (s : Finset X) (W : Set X),
      s.card ≤ b.pieceBound ∧ (↑s : Set X) ⊆ K ∧ IsOpen W ∧ K ⊆ W ∧
      (∀ x ∈ W, ∑ z : s, round4RefinementSquareCutoff X s b.cutoffRadius z x ^ 2 = 1) ∧
      (∀ z : s, ContDiff ℝ ∞ (round4RefinementSquareCutoff X s b.cutoffRadius z)) ∧
      (∀ x : X, (activeCutoffIndices (round4RefinementSquareCutoff X s b.cutoffRadius) x).card ≤
        5^Module.finrank ℝ X) ∧
      (∀ (z : s) j y,
        ‖iteratedFDeriv ℝ j (round4RefinementSquareCutoff X s b.cutoffRadius z) y‖ ≤ b.cutoffProfile j) := by
  classical
  have hRadius := round4UniformNormalRefinementRadius_spec (N := N) b.templateDim b.operatorBound
    b.phaseMargin b.tensorLower b.nativeTensor1 b.phaseMargin_pos b.tensorLower_pos
    b.buffer b.firstLower b.nativeMap3 b.lipschitz b.buffer_pos b.firstLower_pos b.nativeMap3_nonneg
  have hFamily := Classical.choose_spec (round4_uniform_weighted_template_profiles_before_fields
    («Ep» := Ep) (N := N) b.templateDim b.operatorBound b.phaseMargin b.tensorLower b.nativeTensor1
    b.phaseMargin_pos b.tensorLower_pos b.modelRadius b.radius hRadius.1 b.lipschitz hRadius.2.2.1)
  obtain ⟨s,pick,charts,W,label,hBase,hJets⟩ := hFamily (fun _ => u) univ K center isOpen_univ
    (((LipschitzWith.const u).weaken (show 0 ≤ b.lipschitz from zero_le)).lipschitzOnWith)
    contDiffOn_const (fun _ _ v w => hu.2.1 v w) hKball (fun _ _ => subset_univ _) (fun _ _ => hu)
  rcases hBase with ⟨hCard,hCenters,hOpen,hCover,_,_,hPartition,hSmooth,hCount,_⟩
  exact ⟨s,W,hCard,hCenters,hOpen,hCover,hPartition,hSmooth,hCount,hJets⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.sourceCollarNov_budget_refinement
