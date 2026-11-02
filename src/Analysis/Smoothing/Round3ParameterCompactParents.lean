import Smoothing.TensorLocalPrepared
import Smoothing.ParameterRound2CompactPair

/-! The SAME original source/parameter raw preparation supplies compact
physical parents. Compactness follows from the actual fixed Ω/Q sampling
sets. Their sum is one near K, their supports lie in the actual product
charts, and their local count is controlled by the original support degree.
No second parameter cutoff is applied to any constructed increment. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {n d c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)

theorem round3Parameter_product_cutoff_compact
    (A : BufferedAtlas M D) (B : TensorBufferedChartFamily (Fin c) P Ep)
    (chiS : Fin A.count → M → ℝ) (chiP : Fin c → P → ℝ)
    (hS : ∀ i, tsupport (chiS i) ⊆ A.inner i) (hP : ∀ i, tsupport (chiP i) ⊆ B.inner i)
    (Omega : Fin A.count → Set D) (Q : Fin c → Set Ep)
    (hOmega : ∀ i, IsCompact (Omega i)) (hQ : ∀ i, IsCompact (Q i))
    (hOT : ∀ i, Omega i ⊆ (A.chart i).target) (hQT : ∀ i, Q i ⊆ (B.chart i).target)
    (hSource : ∀ i, bufferedSamplingCoordinates A i ⊆ Omega i)
    (hParameter : ∀ i, tensorLocalSamplingCoordinates B i ⊆ Q i)
    (i : Fin A.count × Fin c) :
    IsCompact (tsupport (parameterLocalProductCutoff A B chiS chiP i)) := by
  let q := (B.chart i.2).prod (A.chart i.1)
  have hTarget : Q i.2 ×ˢ Omega i.1 ⊆ q.target := fun z hz => ⟨hQT _ hz.1,hOT _ hz.2⟩
  have hCompact : IsCompact (q.symm '' (Q i.2 ×ˢ Omega i.1)) :=
    ((hQ i.2).prod (hOmega i.1)).image_of_continuousOn (q.symm.continuousOn.mono hTarget)
  apply hCompact.of_isClosed_subset (isClosed_tsupport _)
  intro z hz
  have hh := parameterLocalProductCutoff_tsupport_subset A B chiS chiP i hz
  have hp := hP i.2 hh.1
  have hs := hS i.1 hh.2
  have hps := B.inner_subset i.2 hp
  have hss := A.inner_subset i.1 hs
  refine ⟨q z,?_,q.left_inv ⟨hps,hss⟩⟩
  exact ⟨hParameter i.2 (tensorLocalInner_subset_sampling B i.2 (tensorLocalInner_mem B i.2 hp)),
    hSource i.1 (bufferedInner_subset_sampling A i.1 (bufferedInnerCoordinates_mem A i.1 hs))⟩

def round3ParameterProductParent
    (A : BufferedAtlas M D) (B : TensorBufferedChartFamily (Fin c) P Ep)
    (chiS : Fin A.count → M → ℝ) (chiP : Fin c → P → ℝ)
    (i : Fin A.count × Fin c) (z : P × M) : ℝ :=
  parameterLocalProductCutoff A B chiS chiP i z * parameterLocalProductCutoff A B chiS chiP i z

theorem round3ParameterProductParent_tsupport
    (A : BufferedAtlas M D) (B : TensorBufferedChartFamily (Fin c) P Ep)
    (chiS : Fin A.count → M → ℝ) (chiP : Fin c → P → ℝ) (i : Fin A.count × Fin c) :
    tsupport (round3ParameterProductParent A B chiS chiP i) ⊆
      tsupport (parameterLocalProductCutoff A B chiS chiP i) := tsupport_mul_subset_left

variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local instance round3ParameterCompactParentsChartedSpace : ChartedSpace (Ep × D) (P × M) :=
  prodChartedSpace Ep P D M
local instance round3ParameterCompactParentsIsManifold : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,D)) (n := ∞) P M

theorem round3Parameter_actual_compact_product_parents
    (BS0 TS0 BP0 TP0 : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j) (Ds Dp : ℕ)
    (A : BufferedAtlas M D) (B : TensorBufferedChartFamily (Fin c) P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (K : Set P) (RS : TensorRawCutoffPreparation A BS0 TS0 Ds)
    (RP : TensorLocalRawPreparation B K BP0 TP0 Dp)
    (Omega : Fin A.count → Set D) (Q : Fin c → Set Ep)
    (hOmega : ∀ i, IsCompact (Omega i)) (hQ : ∀ i, IsCompact (Q i))
    (hOT : ∀ i, Omega i ⊆ (A.chart i).target) (hQT : ∀ i, Q i ⊆ (B.chart i).target)
    (hSource : ∀ i, bufferedSamplingCoordinates A i ⊆ Omega i)
    (hParameter : ∀ i, tensorLocalSamplingCoordinates B i ⊆ Q i) :
    let theta := round3ParameterProductParent A B (squareNormalizedCutoff RS.raw)
      (tensorLocalNormalizedCutoff RP.raw)
    ∃ W : Set P, IsOpen W ∧ K ⊆ W ∧
      (∀ i, ContMDiff 𝓘(ℝ,Ep × D) 𝓘(ℝ,ℝ) ∞ (theta i)) ∧
      (∀ i, IsCompact (tsupport (theta i))) ∧
      (∀ i, tsupport (theta i) ⊆ B.inner i.2 ×ˢ A.inner i.1) ∧
      (∀ z : P × M, z.1 ∈ W → ∑ i, theta i z = 1) ∧
      ∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ (Ds+1)*(Dp+1) := by
  intro theta
  obtain ⟨Bj,hBj,hPrep⟩ := exists_uniform_local_product_smoothing_providers
    (Es := D) («Ep» := Ep) (M := M) (P := P)
    BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp
  obtain ⟨W,hW,hKW,hchi,hpart,hsupport,hCount,hJets,hTransition⟩ := hPrep c A B hA hB K RS RP
  let chi := parameterLocalProductCutoff A B (squareNormalizedCutoff RS.raw)
    (tensorLocalNormalizedCutoff RP.raw)
  have hCompact (i) : IsCompact (tsupport (chi i)) :=
    round3Parameter_product_cutoff_compact A B (squareNormalizedCutoff RS.raw)
      (tensorLocalNormalizedCutoff RP.raw)
      (fun i => (squareNormalizedCutoff_tsupport_subset RS.raw i).trans (RS.inner_support i))
      (fun i => (tensorLocalNormalizedCutoff_tsupport_subset RP.raw i).trans (RP.inner_support i))
      Omega Q hOmega hQ hOT hQT hSource hParameter i
  have hSub (i) : tsupport (theta i) ⊆ tsupport (chi i) :=
    round3ParameterProductParent_tsupport A B _ _ i
  refine ⟨W,hW,hKW,fun i => (hchi i).mul (hchi i),
    fun i => (hCompact i).of_isClosed_subset (isClosed_tsupport _) (hSub i),
    fun i => (hSub i).trans (hsupport i),?_,?_⟩
  · intro z hz
    simpa only [theta,round3ParameterProductParent,pow_two] using hpart z hz
  · intro z
    apply (Finset.card_le_card ?_).trans (hCount z)
    intro i hi
    exact (mem_activeCutoffIndices chi z i).2 (hSub i (Finset.mem_filter.mp hi).2)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_actual_compact_product_parents
