import Repair.SourceCollarNovParentCollars
import Repair.SourceCollarNovOriginalDomains

/-! The two actual parent collars combine in the same original product
coordinates. The original atlases and norm domains are unchanged. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Metric Manifold
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

variable {Es Ep M P : Type*}
  [NormedAddCommGroup Es] [NormedSpace ℝ Es] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace Es M] [IsManifold 𝓘(ℝ,Es) ∞ M]
  [TopologicalSpace P] [ChartedSpace Ep P] [IsManifold 𝓘(ℝ,Ep) ∞ P]
  {A : BufferedAtlas M Es} {B : BufferedAtlas P Ep}
  {BS TS BP TP : ℕ → ℝ} {Ds Dp : ℕ}

private local instance novParentProductChart : ChartedSpace (Ep × Es) (P × M) := prodChartedSpace Ep P Es M
private local instance novParentProductManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,Es)) (n := ∞) P M

variable (RS : TensorRawCutoffPreparation A BS TS Ds) (RP : TensorRawCutoffPreparation B BP TP Dp)

def sourceCollarNovParentProduct (i : Fin A.count × Fin B.count) (z : P × M) : ℝ :=
  sourceCollarNovParent RP i.2 z.1 * sourceCollarNovParent RS i.1 z.2

def sourceCollarNovParentProductDomain (i : Fin A.count × Fin B.count) : Set (Ep × Es) :=
  sourceCollarNovParentDomain RP i.2 ×ˢ sourceCollarNovParentDomain RS i.1

def sourceCollarNovParentProductCarrier (i : Fin A.count × Fin B.count) : Set (Ep × Es) :=
  sourceCollarNovParentCarrier RP i.2 ×ˢ sourceCollarNovParentCarrier RS i.1

theorem sourceCollarNovParentProduct_smooth (i : Fin A.count × Fin B.count) :
    ContMDiff (ModelWithCorners.prod 𝓘(ℝ,Ep) 𝓘(ℝ,Es)) 𝓘(ℝ,ℝ) ∞
      (sourceCollarNovParentProduct RS RP i) :=
  ((sourceCollarNovParent_contMDiff RP i.2).comp contMDiff_fst).mul
    ((sourceCollarNovParent_contMDiff RS i.1).comp contMDiff_snd)

theorem sourceCollarNovParentProduct_tsupport (i : Fin A.count × Fin B.count) :
    tsupport (sourceCollarNovParentProduct RS RP i) ⊆
      tsupport (sourceCollarNovParent RP i.2) ×ˢ tsupport (sourceCollarNovParent RS i.1) := by
  intro z hz
  exact ⟨tsupport_comp_subset_preimage _ continuous_fst (tsupport_mul_subset_left hz),
    tsupport_comp_subset_preimage _ continuous_snd (tsupport_mul_subset_right hz)⟩

theorem sourceCollarNovParentProduct_original_support (i : Fin A.count × Fin B.count) :
    tsupport (sourceCollarNovParentProduct RS RP i) ⊆ B.support i.2 ×ˢ A.support i.1 := by
  intro z hz
  have hh := sourceCollarNovParentProduct_tsupport RS RP i hz
  exact ⟨RP.enlarged_support i.2 (sourceCollarNovParent_original_support RP i.2 hh.1),
    RS.enlarged_support i.1 (sourceCollarNovParent_original_support RS i.1 hh.2)⟩

theorem sourceCollarNovParentProduct_square_sum (z : P × M) :
    ∑ i : Fin A.count × Fin B.count, sourceCollarNovParentProduct RS RP i z ^ 2 = 1 := by
  simp only [Fintype.sum_prod_type,sourceCollarNovParentProduct,mul_pow,← Finset.sum_mul,
    sourceCollarNovParent_square_sum,one_mul]

theorem sourceCollarNovParentProduct_domain_open (i : Fin A.count × Fin B.count) :
    IsOpen (sourceCollarNovParentProductDomain RS RP i) :=
  (sourceCollarNovParent_domain_open RP i.2).prod (sourceCollarNovParent_domain_open RS i.1)

theorem sourceCollarNovParentProduct_domain_original (i : Fin A.count × Fin B.count) :
    sourceCollarNovParentProductDomain RS RP i ⊆ sourceCollarNovOriginalOuter A B i := by
  intro z hz
  exact ⟨(sourceCollarNovParent_domain_sampling RP i.2) hz.1,
    (sourceCollarNovParent_domain_sampling RS i.1) hz.2⟩

theorem sourceCollarNovParentProduct_domain_inner (i : Fin A.count × Fin B.count) (z : Ep × Es)
    (hz : z ∈ sourceCollarNovParentProductDomain RS RP i) :
    (B.chart i.2).symm z.1 ∈ B.inner i.2 ∧ (A.chart i.1).symm z.2 ∈ A.inner i.1 :=
  ⟨sourceCollarNovParent_domain_inner RP i.2 ⟨z.1,hz.1,rfl⟩,
    sourceCollarNovParent_domain_inner RS i.1 ⟨z.2,hz.2,rfl⟩⟩

theorem sourceCollarNovParentProduct_carrier_original (i : Fin A.count × Fin B.count) :
    sourceCollarNovParentProductCarrier RS RP i ⊆ sourceCollarNovOriginalInner A B i := by
  intro z hz
  exact ⟨sourceCollarNovParent_carrier_inner RP i.2 hz.1,
    sourceCollarNovParent_carrier_inner RS i.1 hz.2⟩

theorem sourceCollarNovParentProduct_source (i : Fin A.count × Fin B.count) :
    tsupport (sourceCollarNovParentProduct RS RP i) ⊆
      ((B.chart i.2).prod (A.chart i.1)).source ∩
        ((B.chart i.2).prod (A.chart i.1)) ⁻¹' sourceCollarNovParentProductCarrier RS RP i := by
  intro z hz
  have hh := sourceCollarNovParentProduct_tsupport RS RP i hz
  have hp := sourceCollarNovParent_source RP i.2 hh.1
  have hs := sourceCollarNovParent_source RS i.1 hh.2
  exact ⟨⟨hp.1,hs.1⟩,hp.2,hs.2⟩

theorem sourceCollarNovParentProduct_buffer
    (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
    (hBS : 0 ≤ BS 1) (hBP : 0 ≤ BP 1)
    (r : ℝ) (hrS : r ≤ sourceCollarNovParentRadius A BS) (hrP : r ≤ sourceCollarNovParentRadius B BP)
    (i : Fin A.count × Fin B.count) (z : Ep × Es)
    (hz : z ∈ sourceCollarNovParentProductCarrier RS RP i) :
    ball z r ⊆ sourceCollarNovParentProductDomain RS RP i := by
  intro y hy
  have hh : y ∈ ball z.1 r ×ˢ ball z.2 r := by simpa only [ball_prod_same] using hy
  exact ⟨sourceCollarNovParent_buffer hB RP hBP i.2 z.1 hz.1 (ball_subset_ball hrP hh.1),
    sourceCollarNovParent_buffer hA RS hBS i.1 z.2 hz.2 (ball_subset_ball hrS hh.2)⟩

theorem sourceCollarNovParentProduct_compact [T2Space M] [T2Space P]
    (Omega : Fin A.count → Set Es) (Q : Fin B.count → Set Ep)
    (hSC : ∀ i, IsCompact (Omega i)) (hPC : ∀ i, IsCompact (Q i))
    (hST : ∀ i, Omega i ⊆ (A.chart i).target) (hPT : ∀ i, Q i ⊆ (B.chart i).target)
    (hSS : ∀ i, bufferedSamplingCoordinates A i ⊆ Omega i)
    (hPS : ∀ i, bufferedSamplingCoordinates B i ⊆ Q i) (i : Fin A.count × Fin B.count) :
    IsCompact (tsupport (sourceCollarNovParentProduct RS RP i)) :=
  ((sourceCollarNovParent_compact RP Q hPC hPT hPS i.2).prod
    (sourceCollarNovParent_compact RS Omega hSC hST hSS i.1)).of_isClosed_subset
      (isClosed_tsupport _) (sourceCollarNovParentProduct_tsupport RS RP i)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.sourceCollarNovParentProduct_buffer
#print axioms GlobalEmbedding.Continuation.sourceCollarNovParentProduct_square_sum
