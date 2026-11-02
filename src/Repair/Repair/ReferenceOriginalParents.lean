import Smoothing.Round4ParentFiniteProfiles

/-!
# The actual original product parents, with their fixed finite profiles

The two raw preparations determine the literal outer cutoff and its square.
Their supports, partitions, compactness, graph bounds and all receiving-chart
jets are produced here. The parameter preparation covers the whole original
parameter manifold. No normalized cutoff estimate or parent output is an input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {n d c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "IJ" => ModelWithCorners.prod 𝓘(ℝ,Ep) 𝓘(ℝ,D)
private local instance originalParentsChart : ChartedSpace X (P × M) := prodChartedSpace Ep P D M
private local instance originalParentsManifold : IsManifold 𝓘(ℝ,X) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,D)) (n := ∞) P M

/-- Properties of the two literal parent families. The following theorem
constructs this record from the original raw preparations and sampling sets. -/
structure RepairReferenceOriginalParentProperties
    (A : BufferedAtlas M D) (B : TensorBufferedChartFamily (Fin c) P Ep)
    (sourceSupport : Fin A.count → Set M) (parameterSupport : Fin c → Set P)
    (outer theta : (Fin A.count × Fin c) → P × M → ℝ)
    (Outer Parent Transition : ℕ → ℝ) (Ds Dp : ℕ) : Prop where
  outer_smooth : ∀ i, ContMDiff IJ 𝓘(ℝ,ℝ) ∞ (outer i)
  outer_compact : ∀ i, IsCompact (tsupport (outer i))
  outer_partition : ∀ z, ∑ i, outer i z^2=1
  outer_inner : ∀ i, tsupport (outer i) ⊆ B.inner i.2 ×ˢ A.inner i.1
  outer_source : ∀ i, tsupport (outer i) ⊆ (B.chart i.2).source ×ˢ (A.chart i.1).source
  outer_graph_support : ∀ i, tsupport (outer i) ⊆ parameterSupport i.2 ×ˢ sourceSupport i.1
  source_degree : ∀ i, tensorEnlargedSupportDegree sourceSupport i ≤ Ds
  parameter_degree : ∀ i, tensorEnlargedSupportDegree parameterSupport i ≤ Dp
  outer_count : ∀ z, (activeCutoffIndices outer z).card ≤ (Ds+1)*(Dp+1)
  outer_jets : ∀ (p i : Fin A.count × Fin c) j, ∀ y ∈ ((B.chart p.2).prod (A.chart p.1)).target,
    ‖iteratedFDeriv ℝ j (outer i ∘ ((B.chart p.2).prod (A.chart p.1)).symm) y‖ ≤ Outer j
  outer_transition : ∀ (p i : Fin A.count × Fin c) j, 1 ≤ j → ∀ y ∈ ((B.chart p.2).prod (A.chart p.1)).target,
    ((B.chart p.2).prod (A.chart p.1)).symm y ∈ tsupport (outer i) →
    ‖iteratedFDeriv ℝ j (((B.chart i.2).prod (A.chart i.1)) ∘
      ((B.chart p.2).prod (A.chart p.1)).symm) y‖ ≤ Transition j
  theta_eq : ∀ i z, theta i z=outer i z*outer i z
  theta_nonneg : ∀ i z, 0 ≤ theta i z
  theta_subset_outer : ∀ i, tsupport (theta i) ⊆ tsupport (outer i)
  theta_smooth : ∀ i, ContMDiff IJ 𝓘(ℝ,ℝ) ∞ (theta i)
  theta_compact : ∀ i, IsCompact (tsupport (theta i))
  theta_partition : ∀ z, ∑ i, theta i z=1
  theta_inner : ∀ i, tsupport (theta i) ⊆ B.inner i.2 ×ˢ A.inner i.1
  theta_source : ∀ i, tsupport (theta i) ⊆ (B.chart i.2).source ×ˢ (A.chart i.1).source
  theta_count : ∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ (Ds+1)*(Dp+1)
  theta_jets : ∀ (p i : Fin A.count × Fin c) j, ∀ y ∈ ((B.chart p.2).prod (A.chart p.1)).target,
    ‖iteratedFDeriv ℝ j (theta i ∘ ((B.chart p.2).prod (A.chart p.1)).symm) y‖ ≤ Parent j

/-- The original raw source/parameter preparations manufacture every parent
property used by the actual reference and increment factories. The profiles
are the fixed Round4 formulas, independent of both atlas counts and the map. -/
theorem repair_reference_original_product_parents
    (BS TS BP TP : ℕ → ℝ)
    (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (A : BufferedAtlas M D) (B : TensorBufferedChartFamily (Fin c) P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (RS : TensorRawCutoffPreparation A BS TS Ds)
    (RP : TensorLocalRawPreparation B univ BP TP Dp)
    (Omega : Fin A.count → Set D) (Q : Fin c → Set Ep)
    (hOmega : ∀ i, IsCompact (Omega i)) (hQ : ∀ i, IsCompact (Q i))
    (hOT : ∀ i, Omega i ⊆ (A.chart i).target) (hQT : ∀ i, Q i ⊆ (B.chart i).target)
    (hSource : ∀ i, bufferedSamplingCoordinates A i ⊆ Omega i)
    (hParameter : ∀ i, tensorLocalSamplingCoordinates B i ⊆ Q i) :
    RepairReferenceOriginalParentProperties A B A.support RP.enlarged
      (parameterLocalProductCutoff A B (squareNormalizedCutoff RS.raw)
        (tensorLocalNormalizedCutoff RP.raw))
      (round3ParameterProductParent A B (squareNormalizedCutoff RS.raw)
        (tensorLocalNormalizedCutoff RP.raw))
      (round4ProductCutoffProfile BS TS BP TP Ds Dp)
      (round4ParentProfile BS TS BP TP Ds Dp) (fun j => max (TP j) (TS j)) Ds Dp := by
  let outer := parameterLocalProductCutoff A B (squareNormalizedCutoff RS.raw)
    (tensorLocalNormalizedCutoff RP.raw)
  let theta := round3ParameterProductParent A B (squareNormalizedCutoff RS.raw)
    (tensorLocalNormalizedCutoff RP.raw)
  obtain ⟨W,hW,hUW,hSmooth,hPart,hInner,hCount,hJets,hTransition⟩ :=
    round4_actual_product_smoothing_providers BS TS BP TP hBS hTS hBP hTP Ds Dp
      c A B hA hB univ RS RP
  have hCompact (i) : IsCompact (tsupport (outer i)) :=
    round3Parameter_product_cutoff_compact A B _ _
      (fun i => (squareNormalizedCutoff_tsupport_subset RS.raw i).trans (RS.inner_support i))
      (fun i => (tensorLocalNormalizedCutoff_tsupport_subset RP.raw i).trans (RP.inner_support i))
      Omega Q hOmega hQ hOT hQT hSource hParameter i
  have hSub (i) : tsupport (theta i) ⊆ tsupport (outer i) :=
    round3ParameterProductParent_tsupport A B _ _ i
  have hSource' (i) : tsupport (outer i) ⊆ (B.chart i.2).source ×ˢ (A.chart i.1).source := by
    intro z hz
    exact ⟨B.inner_subset i.2 (hInner i hz).1,A.inner_subset i.1 (hInner i hz).2⟩
  refine {
    outer_smooth := ?_
    outer_compact := hCompact
    outer_partition := fun z => hPart z (hUW (mem_univ z.1))
    outer_inner := hInner
    outer_source := hSource'
    outer_graph_support := ?_
    source_degree := fun i => (tensorSupportDegree_le_original A i).trans RS.degree
    parameter_degree := RP.degree
    outer_count := hCount
    outer_jets := ?_
    outer_transition := hTransition
    theta_eq := fun _ _ => rfl
    theta_nonneg := fun i z => mul_self_nonneg (outer i z)
    theta_subset_outer := hSub
    theta_smooth := ?_
    theta_compact := fun i => (hCompact i).of_isClosed_subset (isClosed_tsupport _) (hSub i)
    theta_partition := ?_
    theta_inner := fun i => (hSub i).trans (hInner i)
    theta_source := fun i => (hSub i).trans (hSource' i)
    theta_count := ?_
    theta_jets := ?_ }
  · intro i
    rw [← modelWithCornersSelf_prod]
    exact hSmooth i
  · intro i z hz
    have h := parameterLocalProductCutoff_tsupport_subset A B _ _ i hz
    exact ⟨RP.enlarged_support i.2 (tensorLocalNormalizedCutoff_tsupport_subset RP.raw i.2 h.1),
      RS.enlarged_support i.1 (squareNormalizedCutoff_tsupport_subset RS.raw i.1 h.2)⟩
  · intro p i j y hy
    by_cases hs : ((B.chart p.2).prod (A.chart p.1)).symm y ∈ tsupport (outer i)
    · exact hJets p i j y hy hs
    · rw [iteratedFDeriv_comp_eq_zero_off_tsupport _ _ y
        (((B.chart p.2).prod (A.chart p.1)).symm.continuousAt hy) hs j,norm_zero]
      exact round4ProductCutoffProfile_nonneg hBS hTS hBP hTP Ds Dp j
  · intro i
    rw [← modelWithCornersSelf_prod]
    exact (hSmooth i).mul (hSmooth i)
  · intro z
    simpa only [round3ParameterProductParent,pow_two] using hPart z (hUW (mem_univ z.1))
  · intro z
    apply (Finset.card_le_card ?_).trans (hCount z)
    intro i hi
    exact (mem_activeCutoffIndices outer z i).2 (hSub i (Finset.mem_filter.mp hi).2)
  · intro p i j y hy
    simpa only [parameterLocalProductFamily,one_pow,one_mul] using
      round4_actual_product_parent_jets BS TS BP TP hBS hTS hBP hTP Ds Dp
        A B hA hB univ RS RP p i j 1 zero_le_one le_rfl y hy

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repair_reference_original_product_parents
