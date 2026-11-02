import Repair.SourceCollarNovFactoryGeometry

/-!
# The original reference local factory on an arbitrary buffered open domain

Convexity of the entire original coordinate domain is unnecessary.  The
original buffer supplies a convex ball at each actual refinement center.
The existing normal producer is run there, with the unchanged original
map, tensor, atlas, sample sets, and numerical budget.  Each produced chart
is then regarded inside the original open domain.  All fields of the old
RepairReferenceOriginalLocalFactory are constructed; no collar, local
geometry, cutoff, output derivative bound, or changed norm is assumed.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Metric Bundle
open scoped ContDiff Topology TensorProduct BigOperators ENNReal
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance novBufferedFactoryRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance novBufferedFactorySquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "I" => 𝓘(ℝ,D)
local notation "Edge" => EdgePair (Module.finrank ℝ D+1)
private local instance novBufferedFactoryHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance novBufferedFactoryHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance novBufferedFactoryTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) := inferInstance
private local instance novBufferedFactoryTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) := inferInstance

theorem repair_reference_original_local_factory_buffered
    (b : RepairReferenceFactoryBudget m d N)
    (seed : RepairOriginalReferenceSeed (m+1) d N M P)
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (fun x => seed.F0 (p,x)))
    (S : Fin seed.atlas.count × Fin seed.parameterCount → Set (Fin (m+1+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation seed.atlas seed.parameterChart i)
    (hCoords : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates seed.atlas seed.parameterChart seed.F0 i)
      (incrementsOriginalDifferentiation seed.atlas seed.parameterChart i))
    (hC3 : paperAtlasCj 3 (incrementsOriginalMapCoordinates seed.atlas seed.parameterChart seed.F0)
      (incrementsOriginalDifferentiation seed.atlas seed.parameterChart) S ≤ ENNReal.ofReal b.mapC3)
    (Htensor : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (hTensorCoords : ∀ a, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates seed.atlas seed.parameterChart Htensor a)
      (incrementsOriginalDifferentiation seed.atlas seed.parameterChart a))
    (hC1 : paperAtlasCj 1 (incrementsOriginalTensorCoordinates seed.atlas seed.parameterChart Htensor)
      (incrementsOriginalDifferentiation seed.atlas seed.parameterChart) S ≤ ENNReal.ofReal b.tensorC1)
    (hSymm : ∀ p x, (Htensor p x).IsSymm)
    (i : Fin seed.atlas.count × Fin seed.parameterCount)
    (hhost : seed.atlas.chart i.1 ∈ IsManifold.maximalAtlas I ∞ M)
    (O K : Set X) (center : X)
    (hO : IsOpen O)
    (hSample : ∀ z ∈ O, parameterTensorModelEquiv (m+1) d z ∈ S i)
    (hKball : K ⊆ closedBall center b.modelRadius)
    (hBuffer : ∀ x ∈ K, ball x b.buffer ⊆ O)
    (hPhase : ∀ x ∈ K, b.phaseMargin ≤ bestPhaseSupremum (repairReferenceFactoryField seed Htensor i x).1)
    (hPositive : ∀ x ∈ K, ∀ v : D,
      b.tensorLower*‖v‖^2 ≤ round4OriginalNativeTensorCoordinates seed.atlas seed.parameterChart Htensor i x v v)
    (hFirst : ∀ z ∈ O, ∀ v : D, b.firstLower*‖v‖^2 ≤
      ‖fderiv ℝ ((fun x => seed.F0 ((seed.parameterChart i.2).symm z.1,x)) ∘
        (seed.atlas.chart i.1).symm) z.2 v‖^2) :
    Nonempty (RepairReferenceOriginalLocalFactory b seed hF Htensor S i O K center) := by
  classical
  have hKO : K ⊆ O := fun x hx => hBuffer x hx (mem_ball_self b.buffer_pos)
  have hJoint := round4_original_native_host_joint_smooth seed.atlas seed.parameterChart
    seed.F0 S hSO hCoords i O hSample
  have hC2 : ∀ z ∈ O, ‖iteratedFDeriv ℝ 2 (round3OriginalNativeMapCoordinates
      seed.atlas seed.parameterChart seed.F0 i) z‖ ≤ b.nativeMap3 := by
    intro z hz
    exact round4_original_C3_native_joint_jets seed.atlas seed.parameterChart seed.F0 S hSO hCoords
      b.mapC3 b.mapC3_nonneg hC3 i 2 (by omega) z (hSample z hz)
  have hOperator : ∀ z ∈ O, ‖(repairReferenceFactoryField seed Htensor i z).1‖ ≤ b.operatorBound := by
    intro z hz
    exact round4_actual_phase_operator_norm_from_joint_C2
      (fun p x => seed.F0 ((seed.parameterChart i.2).symm p,x)) (seed.atlas.chart i.1)
      O hO hJoint b.nativeMap3 hC2 z hz
  by_cases hK : K.Nonempty
  · obtain ⟨x0,hx0⟩ := hK
    have hTensor := round4_original_tensor_native_jets seed.atlas seed.parameterChart Htensor S hSO
      hTensorCoords 1 b.tensorC1 b.tensorC1_nonneg hC1 i O hO hSample
    have hAllowed : repairReferenceFactoryField seed Htensor i x0 ∈
        actualAllowedPhaseTensorData D V b.operatorBound b.phaseMargin b.tensorLower b.nativeTensor1 := by
      refine ⟨⟨hOperator x0 (hKO hx0),hPhase x0 hx0⟩,?_,hPositive x0 hx0,?_⟩
      · exact round4_original_native_tensor_isSymm seed.atlas seed.parameterChart Htensor i x0 (hSymm _ _)
      · change ‖round4OriginalNativeTensorCoordinates seed.atlas seed.parameterChart Htensor i x0‖ ≤
          round4OriginalTensorJetCost (m+1) d 1*b.tensorC1
        simpa only [norm_iteratedFDeriv_zero] using hTensor.2 0 (by omega) x0 (hKO hx0)
    obtain ⟨s,W,hCard,hCenters,hOpen,hCover,hPartition,hSmooth,hCount,hCutoffJets⟩ :=
      sourceCollarNov_budget_refinement b _ hAllowed K center hKball
    have hLocal (z : s) : Nonempty (RepairReferenceOriginalLocalFactory b seed hF Htensor S i
        (ball z.val b.buffer) {z.val} center) := by
      apply repair_reference_original_local_factory b seed hF S hSO hCoords hC3 Htensor hTensorCoords
        hC1 hSymm i hhost (ball z.val b.buffer) {z.val} center isOpen_ball (convex_ball _ _)
      · intro y hy
        exact hSample y (hBuffer z.val (hCenters z.property) hy)
      · intro y hy
        exact hKball (by simpa only [mem_singleton_iff.mp hy] using hCenters z.property)
      · intro y hy
        rcases mem_singleton_iff.mp hy with rfl
        exact Subset.rfl
      · intro y hy
        simpa only [mem_singleton_iff.mp hy] using hPhase z.val (hCenters z.property)
      · intro y hy v
        simpa only [mem_singleton_iff.mp hy] using hPositive z.val (hCenters z.property) v
      · intro y hy v
        exact hFirst y (hBuffer z.val (hCenters z.property) hy) v
    let localData (z : s) := Classical.choice (hLocal z)
    have hCenterMem (z : s) : z.val ∈ (localData z).s := by
      by_contra hn
      have hEmpty (q : (localData z).s) : False := by
        have hq : q.val = z.val := (localData z).centers q.property
        exact hn (by simpa only [hq] using q.property)
      letI : IsEmpty (localData z).s := ⟨hEmpty⟩
      have hh := (localData z).square_partition z.val ((localData z).cover (mem_singleton z.val))
      simpa using hh
    let localIndex (z : s) : (localData z).s := ⟨z.val,hCenterMem z⟩
    let pick (z : s) := (localData z).pick (localIndex z)
    let charts (z : s) (a : Edge) := sourceCollarNov_lift_chart b
      ((localData z).charts (localIndex z) a) (hBuffer z.val (hCenters z.property))
    refine ⟨{
      s := s
      pick := pick
      charts := charts
      W := W ∩ O
      card := hCard
      centers := hCenters
      open_partition := hOpen.inter hO
      cover := fun _ hx => ⟨hCover hx,hKO hx⟩
      partition_domain := inter_subset_right
      operator_bound := hOperator
      square_partition := fun x hx => hPartition x hx.1
      cutoff_smooth := hSmooth
      local_count := hCount
      normal := fun z a => (localData z).normal (localIndex z) a
      normal_support := ?_
      normal_jets := ?_
      cutoff_jets := hCutoffJets
      chart_profiles := ?_ }⟩
    · intro z a
      have hh := (localData z).normal_support (localIndex z) a
      rw [sourceCollarNov_square_tsupport X s b.cutoffRadius b.cutoffRadius_pos z]
      rw [sourceCollarNov_square_tsupport X (localData z).s b.cutoffRadius
        b.cutoffRadius_pos (localIndex z)] at hh
      exact hh
    · intro j Rj hRj hNorm z a k hk y hy
      exact (localData z).normal_jets j Rj hRj hNorm (localIndex z) a k hk y hy
    · intro B0 hCenter z a
      exact (localData z).chart_profiles B0 hCenter (localIndex z) a
  · have hEmpty : K = ∅ := not_nonempty_iff_eq_empty.mp hK
    refine ⟨{
      s := ∅
      pick := fun z => False.elim (Finset.notMem_empty z.val z.property)
      charts := fun z => False.elim (Finset.notMem_empty z.val z.property)
      W := ∅
      card := Nat.zero_le _
      centers := by simp
      open_partition := isOpen_empty
      cover := by simp only [hEmpty, subset_refl]
      partition_domain := empty_subset _
      operator_bound := hOperator
      square_partition := fun _ hx => False.elim hx
      cutoff_smooth := fun z => False.elim (Finset.notMem_empty z.val z.property)
      local_count := ?_
      normal := fun z => False.elim (Finset.notMem_empty z.val z.property)
      normal_support := fun z => False.elim (Finset.notMem_empty z.val z.property)
      normal_jets := ?_
      cutoff_jets := fun z => False.elim (Finset.notMem_empty z.val z.property)
      chart_profiles := ?_ }⟩
    · intro x
      simp [activeCutoffIndices]
    · intro j Rj hRj hNorm z
      exact False.elim (Finset.notMem_empty z.val z.property)
    · intro B0 hCenter z
      exact False.elim (Finset.notMem_empty z.val z.property)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repair_reference_original_local_factory_buffered
