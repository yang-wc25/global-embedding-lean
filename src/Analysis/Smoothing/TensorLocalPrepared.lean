import Smoothing.ParameterLocalCutoffs
import Smoothing.TensorLocalNative

/-!
# Uniform real local parameter preparation from raw geometry

Raw own-chart bounds, actual chart transitions, and actual enlarged-support
degree supply the derivatives of the real local normalization. Parameter
plateaus cover only the requested set Q. Constants precede the chart family,
Q, raw functions, and every smoothing input or scale.
-/

open Module Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Continuation Function Set
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Offline
noncomputable section
set_option backward.isDefEq.respectTransparency false

section LocalCutoff
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℝ, E) ∞ X]

/-- Real mixed-chart derivative bounds for the local normalized cutoffs;
neither a global cover nor a normalized derivative bound is an input. -/
theorem exists_uniform_local_normalized_cutoff_provider
    (B₀ T : ℕ → ℝ) (hB₀ : ∀ j, 0 ≤ B₀ j) (hT : ∀ j, 0 ≤ T j) (D : ℕ) :
    ∃ N : ℕ → ℝ, (∀ j, 0 ≤ N j) ∧
      ∀ (ι : Type*) [Fintype ι] (C : TensorBufferedChartFamily ι X E)
        (hC : ∀ i, C.chart i ∈ maximalAtlas 𝓘(ℝ, E) ∞ X)
        (raw : ι → X → ℝ),
      (∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (raw i)) →
      (∀ i, tsupport (raw i) ⊆ C.inner i) →
      (∀ x, (activeCutoffIndices raw x).card ≤ D) →
      (∀ i j, ∀ y ∈ (C.chart i).target, ‖iteratedFDeriv ℝ j (raw i ∘ (C.chart i).symm) y‖ ≤ B₀ j) →
      (∀ p i j, 1 ≤ j → ∀ y ∈ (C.chart p).target, (C.chart p).symm y ∈ tsupport (raw i) →
        ‖iteratedFDeriv ℝ j (C.chart i ∘ (C.chart p).symm) y‖ ≤ T j) →
      ∀ p i j, ∀ y ∈ (C.chart p).target,
        ‖iteratedFDeriv ℝ j (tensorLocalNormalizedCutoff raw i ∘ (C.chart p).symm) y‖ ≤ N j := by
  obtain ⟨L,hL,htransfer⟩ := exists_actualChart_cutoff_transfer_bounds (E := E) (M := X) B₀ T hB₀ hT
  obtain ⟨N,hN,hnormal⟩ := exists_tensorLocalNormalizedCutoff_derivative_bounds (E := E) (X := X) L hL D
  refine ⟨N,hN,?_⟩
  intro ι _ C hC raw hsmooth hsupp hD hown htrans p
  apply hnormal ι raw (C.chart p).symm (C.chart p).target (C.chart p).open_target
    (fun i => ((hsmooth i).comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hC p))).contDiffOn)
    (C.chart p).symm.continuousOn (fun y _ => hD _) ?_
  intro i y hy hi j
  have hiS := C.inner_subset i (hsupp i hi)
  have h := htransfer 1 le_rfl (raw i) (hsmooth i) (C.chart p) (C.chart i) (hC p) (hC i)
    y ⟨hy,hiS⟩ (fun k => by simpa only [one_pow,mul_one] using hown i k _ ((C.chart i).map_source hiS))
    (fun k hk => htrans p i k hk y hy hi) j
  simpa only [one_pow,mul_one] using h

/-- Real local raw geometry, with only Q covered by unit plateaus. -/
structure TensorLocalRawPreparation {ι : Type*} [Fintype ι]
    (C : TensorBufferedChartFamily ι X E) (Q : Set X) (B₀ T : ℕ → ℝ) (D : ℕ) where
  raw : ι → X → ℝ
  smooth : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (raw i)
  plateau_on : ∀ x ∈ Q, ∃ i, raw i x = 1
  inner_support : ∀ i, tsupport (raw i) ⊆ C.inner i
  enlarged : ι → Set X
  enlarged_support : ∀ i, tsupport (raw i) ⊆ enlarged i
  degree : ∀ i, tensorEnlargedSupportDegree enlarged i ≤ D
  own_jets : ∀ i j, ∀ y ∈ (C.chart i).target, ‖iteratedFDeriv ℝ j (raw i ∘ (C.chart i).symm) y‖ ≤ B₀ j
  transition_jets : ∀ p i j, 1 ≤ j → ∀ y ∈ (C.chart p).target,
    (C.chart p).symm y ∈ tsupport (raw i) →
    ‖iteratedFDeriv ℝ j (C.chart i ∘ (C.chart p).symm) y‖ ≤ T j

end LocalCutoff

variable {Ep Es P M : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Es] [NormedSpace ℝ Es]
  [TopologicalSpace P] [TopologicalSpace M]
  [ChartedSpace Ep P] [IsManifold 𝓘(ℝ, Ep) ∞ P]
  [ChartedSpace Es M] [IsManifold 𝓘(ℝ, Es) ∞ M] {pcount : ℕ}

local instance tensorLocalPreparedChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance tensorLocalPreparedManifold : IsManifold 𝓘(ℝ, Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Ep)) (I' := 𝓘(ℝ, Es)) (n := ∞) P M

theorem tensorLocalProductCutoff_jet_bound
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ j, B.chart j ∈ maximalAtlas 𝓘(ℝ, Ep) ∞ P)
    (chiS : Fin A.count → M → ℝ) (chiP : Fin pcount → P → ℝ)
    (hchiS : ∀ i, ContMDiff 𝓘(ℝ, Es) 𝓘(ℝ, ℝ) ∞ (chiS i))
    (hchiP : ∀ i, ContMDiff 𝓘(ℝ, Ep) 𝓘(ℝ, ℝ) ∞ (chiP i))
    (BS BP : ℕ → ℝ) (hBS : ∀ j, 0 ≤ BS j) (hBP : ∀ j, 0 ≤ BP j)
    (hS : ∀ p i k, ∀ y ∈ bufferedInnerCoordinates A p, (A.chart p).symm y ∈ tsupport (chiS i) →
      ‖iteratedFDeriv ℝ k (chiS i ∘ (A.chart p).symm) y‖ ≤ BS k)
    (hP : ∀ p i k, ∀ y ∈ tensorLocalInner B p, (B.chart p).symm y ∈ tsupport (chiP i) →
      ‖iteratedFDeriv ℝ k (chiP i ∘ (B.chart p).symm) y‖ ≤ BP k) :
    ∀ p i k, ∀ y ∈ tensorLocalInner (parameterLocalProductFamily A B) p,
      ((parameterLocalProductFamily A B).chart p).symm y ∈ tsupport (parameterLocalProductCutoff A B chiS chiP i) →
      ‖iteratedFDeriv ℝ k (parameterLocalProductCutoff A B chiS chiP i ∘
        ((parameterLocalProductFamily A B).chart p).symm) y‖ ≤ tensorProductJetConstant BP BS k := by
  intro p i k y hy hi
  rw [parameterLocalProductFamily_inner] at hy
  have his := parameterLocalProductCutoff_tsupport_subset A B chiS chiP i hi
  have hfs : ContDiffOn ℝ ∞ (chiS i.1 ∘ (A.chart p.1).symm) (A.chart p.1).target :=
    ((hchiS _).comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem _))).contDiffOn
  have hfp : ContDiffOn ℝ ∞ (chiP i.2 ∘ (B.chart p.2).symm) (B.chart p.2).target :=
    ((hchiP _).comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hB _))).contDiffOn
  exact tensor_product_scalar_jet_le (B.chart p.2).open_target (A.chart p.1).open_target
    hfp hfs hy.1.1 hy.2.1 BP BS hBP hBS
    (fun j => hP _ _ j _ hy.1 his.1) (fun j => hS _ _ j _ hy.2 his.2) k

theorem tensorLocalProductTransition_jet_bound
    [MeasurableSpace Ep] [BorelSpace Ep] [FiniteDimensional ℝ Ep]
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ j, B.chart j ∈ maximalAtlas 𝓘(ℝ, Ep) ∞ P)
    (chiS : Fin A.count → M → ℝ) (chiP : Fin pcount → P → ℝ)
    (hSuppS : ∀ i, tsupport (chiS i) ⊆ A.inner i) (hSuppP : ∀ i, tsupport (chiP i) ⊆ B.inner i)
    (TS TP : ℕ → ℝ)
    (hS : ∀ p i k, 1 ≤ k → ∀ y ∈ bufferedInnerCoordinates A p, (A.chart p).symm y ∈ tsupport (chiS i) →
      ‖iteratedFDeriv ℝ k (A.chart i ∘ (A.chart p).symm) y‖ ≤ TS k)
    (hP : ∀ p i k, 1 ≤ k → ∀ y ∈ tensorLocalInner B p, (B.chart p).symm y ∈ tsupport (chiP i) →
      ‖iteratedFDeriv ℝ k (B.chart i ∘ (B.chart p).symm) y‖ ≤ TP k) :
    ∀ p i k, 1 ≤ k → ∀ y ∈ tensorLocalInner (parameterLocalProductFamily A B) p,
      ((parameterLocalProductFamily A B).chart p).symm y ∈ tsupport (parameterLocalProductCutoff A B chiS chiP i) →
      ‖iteratedFDeriv ℝ k ((parameterLocalProductFamily A B).chart i ∘
        ((parameterLocalProductFamily A B).chart p).symm) y‖ ≤ max (TP k) (TS k) := by
  intro p i k hk y hy hi
  rw [parameterLocalProductFamily_inner] at hy
  have his := parameterLocalProductCutoff_tsupport_subset A B chiS chiP i hi
  exact tensor_product_map_jet_le (tensorLocalChartOverlap_open B _ _) (bufferedChartOverlap_open A _ _)
    (tensorLocalTransition_contDiffOn B hB _ _) (bufferedTransition_contDiffOn A hA _ _)
    ⟨hy.1.1,hSuppP _ his.1⟩ ⟨hy.2.1,hSuppS _ his.2⟩ k (TP k) (TS k)
    (hP _ _ k hk _ hy.1 his.1) (hS _ _ k hk _ hy.2 his.2)

/-- The actual local product provides every geometry premise for both map
and tensor smoothing, uniformly before A, B, Q, or any raw functions. -/
theorem exists_uniform_local_product_smoothing_providers
    [MeasurableSpace Ep] [BorelSpace Ep] [FiniteDimensional ℝ Ep]
    (BS₀ TS BP₀ TP : ℕ → ℝ)
    (hBS₀ : ∀ j, 0 ≤ BS₀ j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP₀ : ∀ j, 0 ≤ BP₀ j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ) :
    ∃ Bjoint : ℕ → ℝ, (∀ j, 0 ≤ Bjoint j) ∧
      ∀ (pcount : ℕ) (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
        (hA : IsSmoothBufferedAtlas A) (hB : ∀ j, B.chart j ∈ maximalAtlas 𝓘(ℝ, Ep) ∞ P)
        (Q : Set P) (RS : TensorRawCutoffPreparation A BS₀ TS Ds)
        (RP : TensorLocalRawPreparation B Q BP₀ TP Dp),
      let chi := parameterLocalProductCutoff A B (squareNormalizedCutoff RS.raw) (tensorLocalNormalizedCutoff RP.raw)
      ∃ W : Set P, IsOpen W ∧ Q ⊆ W ∧
      (∀ i, ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, ℝ) ∞ (chi i)) ∧
      (∀ z : P × M, z.1 ∈ W → ∑ i, chi i z ^ 2 = 1) ∧
      (∀ i, tsupport (chi i) ⊆ (parameterLocalProductFamily A B).inner i) ∧
      (∀ z, (activeCutoffIndices chi z).card ≤ (Ds+1)*(Dp+1)) ∧
      (∀ p i k, ∀ y ∈ tensorLocalInner (parameterLocalProductFamily A B) p,
        ((parameterLocalProductFamily A B).chart p).symm y ∈ tsupport (chi i) →
        ‖iteratedFDeriv ℝ k (chi i ∘ ((parameterLocalProductFamily A B).chart p).symm) y‖ ≤ Bjoint k) ∧
      (∀ p i k, 1 ≤ k → ∀ y ∈ tensorLocalInner (parameterLocalProductFamily A B) p,
        ((parameterLocalProductFamily A B).chart p).symm y ∈ tsupport (chi i) →
        ‖iteratedFDeriv ℝ k ((parameterLocalProductFamily A B).chart i ∘
          ((parameterLocalProductFamily A B).chart p).symm) y‖ ≤ max (TP k) (TS k)) := by
  obtain ⟨BS,hBS,hS⟩ := exists_uniform_prepared_tensor_cutoffs (E := Es) (X := M) BS₀ TS hBS₀ hTS Ds
  obtain ⟨BP,hBP,hP⟩ := exists_uniform_local_normalized_cutoff_provider (E := Ep) (X := P) BP₀ TP hBP₀ hTP (Dp+1)
  refine ⟨tensorProductJetConstant BP BS,tensorProductJetConstant_nonneg hBP hBS,?_⟩
  intro pcount A B hA hB Q RS RP
  obtain ⟨hSs,hSpart,hSsupp,hSD,hSj⟩ := hS A hA RS
  have hPD := activeCutoffIndices_card_le_enlarged_degree RP.enlarged RP.raw RP.enlarged_support Dp RP.degree
  have hPj := hP (Fin pcount) B hB RP.raw RP.smooth RP.inner_support hPD RP.own_jets RP.transition_jets
  have hPs := tensorLocalNormalizedCutoff_contMDiff RP.raw RP.smooth
  have hPsupp : ∀ i, tsupport (tensorLocalNormalizedCutoff RP.raw i) ⊆ B.inner i :=
    fun i => (tensorLocalNormalizedCutoff_tsupport_subset RP.raw i).trans (RP.inner_support i)
  obtain ⟨W,hW,hQW,hchi,hpart,hsupp,hD⟩ := parameterLocalProductCutoff_preparation_near A B
    (squareNormalizedCutoff RS.raw) RP.raw hSs RP.smooth hSpart hSsupp RP.inner_support
    (Ds+1) (Dp+1) hSD hPD Q RP.plateau_on
  refine ⟨W,hW,hQW,hchi,hpart,hsupp,hD,?_,?_⟩
  · exact tensorLocalProductCutoff_jet_bound A B hA hB _ _ hSs hPs BS BP hBS hBP hSj
      (fun p i k y hy _ => hPj p i k y hy.1)
  · exact tensorLocalProductTransition_jet_bound A B hA hB _ _ hSsupp hPsupp TS TP
      (fun p i k hk y hy hi => RS.transition_jets p i k hk y hy.1
        (squareNormalizedCutoff_tsupport_subset RS.raw i hi))
      (fun p i k hk y hy hi => RP.transition_jets p i k hk y hy.1
        (tensorLocalNormalizedCutoff_tsupport_subset RP.raw i hi))

#print axioms exists_uniform_local_normalized_cutoff_provider
#print axioms exists_uniform_local_product_smoothing_providers

end
end GlobalEmbedding.Offline
