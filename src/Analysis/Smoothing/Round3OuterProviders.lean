import Smoothing.TensorLocalPrepared

/-! The actual raw cutoffs and active chart transitions supply normalized
cutoff bounds on full receiving targets. Constants are selected before the
atlas and its chart count; the literal normalizations remain unchanged. -/

noncomputable section
open Module Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Continuation Function Set Filter
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Offline
section Source
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
theorem round3Outer_exists_uniform_tensor_cutoff_provider
    (B₀ T : ℕ → ℝ) (hB₀ : ∀ j, 0 ≤ B₀ j) (hT : ∀ j, 0 ≤ T j) (D : ℕ) :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧
      ∀ (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A),
      ∀ (f : Fin A.count → M → ℝ),
      (∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (f i)) →
      (∀ x, ∃ i, f i x = 1) →
      (∀ i, tsupport (f i) ⊆ A.inner i) →
      ∀ W : Fin A.count → Set M,
      (∀ i, tsupport (f i) ⊆ W i) →
      (∀ i, tensorEnlargedSupportDegree W i ≤ D) →
      (∀ i j, ∀ y ∈ (A.chart i).target,
        ‖iteratedFDeriv ℝ j (f i ∘ (A.chart i).symm) y‖ ≤ B₀ j) →
      (∀ p i j, 1 ≤ j → ∀ y ∈ (A.chart p).target,
        (A.chart p).symm y ∈ tsupport (f i) →
        ‖iteratedFDeriv ℝ j (A.chart i ∘ (A.chart p).symm) y‖ ≤ T j) →
      let chi := squareNormalizedCutoff f
      (∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i)) ∧
      (∀ x, ∑ i, chi i x ^ 2 = 1) ∧
      (∀ i, tsupport (chi i) ⊆ A.inner i) ∧
      (∀ x, (activeCutoffIndices chi x).card ≤ D + 1) ∧
      (∀ p i j, ∀ y ∈ (A.chart p).target,
        (A.chart p).symm y ∈ tsupport (chi i) →
        ‖iteratedFDeriv ℝ j (chi i ∘ (A.chart p).symm) y‖ ≤ B j) := by
  obtain ⟨C, hC, hnormalize⟩ := exists_normalizedCutoff_bounds_from_chartProviders
    (E := E) (M := M) B₀ T hB₀ hT (D + 1)
  obtain ⟨B, hB, htransfer⟩ := exists_actualChart_cutoff_transfer_bounds
    (E := E) (M := M) C T hC hT
  refine ⟨B, hB, ?_⟩
  intro A hA f hf hcover hinner W hsupp hdegree hown htrans
  obtain ⟨hchi, hpartition, _, hsupport, hownChi⟩ := hnormalize (Fin A.count) 1 le_rfl f hf hcover
    (activeCutoffIndices_card_le_enlarged_degree W f hsupp D hdegree)
    A.chart hA.chart_mem (fun i => (hinner i).trans (A.inner_subset i))
    (by simpa only [one_pow, mul_one] using hown) htrans
  refine ⟨hchi, hpartition, fun i => (hsupport i).trans (hinner i),
    squareNormalizedCutoff_card_le_enlarged_degree W f hsupp D hdegree, ?_⟩
  intro p i j y hy hi
  have hiRaw := hsupport i hi
  have hiS : (A.chart p).symm y ∈ (A.chart i).source := A.inner_subset i (hinner i hiRaw)
  have h := htransfer 1 le_rfl (squareNormalizedCutoff f i) (hchi i) (A.chart p) (A.chart i)
    (hA.chart_mem p) (hA.chart_mem i) y ⟨hy, hiS⟩
    (fun k => hownChi i k _ ((A.chart i).map_source hiS))
    (fun k hk => htrans p i k hk y hy hiRaw) j
  simpa only [one_pow, mul_one] using h


variable {X : Type*} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℝ,E) ∞ X]

theorem round3Outer_exists_uniform_prepared_tensor_cutoffs
    (B₀ T : ℕ → ℝ) (hB₀ : ∀ j, 0 ≤ B₀ j) (hT : ∀ j, 0 ≤ T j) (D : ℕ) :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧
      ∀ (A : BufferedAtlas X E) (hA : IsSmoothBufferedAtlas A)
        (R : TensorRawCutoffPreparation A B₀ T D),
      let chi := squareNormalizedCutoff R.raw
      (∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i)) ∧
      (∀ x, ∑ i, chi i x ^ 2 = 1) ∧
      (∀ i, tsupport (chi i) ⊆ A.inner i) ∧
      (∀ x, (activeCutoffIndices chi x).card ≤ D + 1) ∧
      (∀ p i j, ∀ y ∈ (A.chart p).target,
        (A.chart p).symm y ∈ tsupport (chi i) →
        ‖iteratedFDeriv ℝ j (chi i ∘ (A.chart p).symm) y‖ ≤ B j) := by
  obtain ⟨B, hB, h⟩ := round3Outer_exists_uniform_tensor_cutoff_provider
    (E := E) (M := X) B₀ T hB₀ hT D
  refine ⟨B, hB, fun A hA R => ?_⟩
  exact h A hA R.raw R.smooth R.plateau_cover R.inner_support A.support R.enlarged_support
    (fun i => (tensorSupportDegree_le_original A i).trans R.degree) R.own_jets R.transition_jets

end Source

variable {Ep Es P M : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Es] [NormedSpace ℝ Es]
  [TopologicalSpace P] [TopologicalSpace M]
  [ChartedSpace Ep P] [IsManifold 𝓘(ℝ, Ep) ∞ P]
  [ChartedSpace Es M] [IsManifold 𝓘(ℝ, Es) ∞ M] {pcount : ℕ}

local instance round3Outer_tensorLocalPreparedChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3Outer_tensorLocalPreparedManifold : IsManifold 𝓘(ℝ, Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Ep)) (I' := 𝓘(ℝ, Es)) (n := ∞) P M

theorem round3Outer_tensorLocalProductCutoff_jet_bound
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ j, B.chart j ∈ maximalAtlas 𝓘(ℝ, Ep) ∞ P)
    (chiS : Fin A.count → M → ℝ) (chiP : Fin pcount → P → ℝ)
    (hchiS : ∀ i, ContMDiff 𝓘(ℝ, Es) 𝓘(ℝ, ℝ) ∞ (chiS i))
    (hchiP : ∀ i, ContMDiff 𝓘(ℝ, Ep) 𝓘(ℝ, ℝ) ∞ (chiP i))
    (BS BP : ℕ → ℝ) (hBS : ∀ j, 0 ≤ BS j) (hBP : ∀ j, 0 ≤ BP j)
    (hS : ∀ p i k, ∀ y ∈ (A.chart p).target, (A.chart p).symm y ∈ tsupport (chiS i) →
      ‖iteratedFDeriv ℝ k (chiS i ∘ (A.chart p).symm) y‖ ≤ BS k)
    (hP : ∀ p i k, ∀ y ∈ (B.chart p).target, (B.chart p).symm y ∈ tsupport (chiP i) →
      ‖iteratedFDeriv ℝ k (chiP i ∘ (B.chart p).symm) y‖ ≤ BP k) :
    ∀ p i k, ∀ y ∈ ((parameterLocalProductFamily A B).chart p).target,
      ((parameterLocalProductFamily A B).chart p).symm y ∈ tsupport (parameterLocalProductCutoff A B chiS chiP i) →
      ‖iteratedFDeriv ℝ k (parameterLocalProductCutoff A B chiS chiP i ∘
        ((parameterLocalProductFamily A B).chart p).symm) y‖ ≤ tensorProductJetConstant BP BS k := by
  intro p i k y hy hi
  have his := parameterLocalProductCutoff_tsupport_subset A B chiS chiP i hi
  have hfs : ContDiffOn ℝ ∞ (chiS i.1 ∘ (A.chart p.1).symm) (A.chart p.1).target :=
    ((hchiS _).comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem _))).contDiffOn
  have hfp : ContDiffOn ℝ ∞ (chiP i.2 ∘ (B.chart p.2).symm) (B.chart p.2).target :=
    ((hchiP _).comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hB _))).contDiffOn
  exact tensor_product_scalar_jet_le (B.chart p.2).open_target (A.chart p.1).open_target
    hfp hfs hy.1 hy.2 BP BS hBP hBS
    (fun j => hP _ _ j _ hy.1 his.1) (fun j => hS _ _ j _ hy.2 his.2) k

theorem round3Outer_tensorLocalProductTransition_jet_bound
    [MeasurableSpace Ep] [BorelSpace Ep] [FiniteDimensional ℝ Ep]
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ j, B.chart j ∈ maximalAtlas 𝓘(ℝ, Ep) ∞ P)
    (chiS : Fin A.count → M → ℝ) (chiP : Fin pcount → P → ℝ)
    (hSuppS : ∀ i, tsupport (chiS i) ⊆ A.inner i) (hSuppP : ∀ i, tsupport (chiP i) ⊆ B.inner i)
    (TS TP : ℕ → ℝ)
    (hS : ∀ p i k, 1 ≤ k → ∀ y ∈ (A.chart p).target, (A.chart p).symm y ∈ tsupport (chiS i) →
      ‖iteratedFDeriv ℝ k (A.chart i ∘ (A.chart p).symm) y‖ ≤ TS k)
    (hP : ∀ p i k, 1 ≤ k → ∀ y ∈ (B.chart p).target, (B.chart p).symm y ∈ tsupport (chiP i) →
      ‖iteratedFDeriv ℝ k (B.chart i ∘ (B.chart p).symm) y‖ ≤ TP k) :
    ∀ p i k, 1 ≤ k → ∀ y ∈ ((parameterLocalProductFamily A B).chart p).target,
      ((parameterLocalProductFamily A B).chart p).symm y ∈ tsupport (parameterLocalProductCutoff A B chiS chiP i) →
      ‖iteratedFDeriv ℝ k ((parameterLocalProductFamily A B).chart i ∘
        ((parameterLocalProductFamily A B).chart p).symm) y‖ ≤ max (TP k) (TS k) := by
  intro p i k hk y hy hi
  have his := parameterLocalProductCutoff_tsupport_subset A B chiS chiP i hi
  exact tensor_product_map_jet_le (tensorLocalChartOverlap_open B _ _) (bufferedChartOverlap_open A _ _)
    (tensorLocalTransition_contDiffOn B hB _ _) (bufferedTransition_contDiffOn A hA _ _)
    ⟨hy.1,hSuppP _ his.1⟩ ⟨hy.2,hSuppS _ his.2⟩ k (TP k) (TS k)
    (hP _ _ k hk _ hy.1 his.1) (hS _ _ k hk _ hy.2 his.2)

/-- The actual local product provides every geometry premise for both map
and tensor smoothing, uniformly before A, B, Q, or any raw functions. -/
theorem round3Outer_exists_uniform_local_product_smoothing_providers
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
      (∀ p i k, ∀ y ∈ ((parameterLocalProductFamily A B).chart p).target,
        ((parameterLocalProductFamily A B).chart p).symm y ∈ tsupport (chi i) →
        ‖iteratedFDeriv ℝ k (chi i ∘ ((parameterLocalProductFamily A B).chart p).symm) y‖ ≤ Bjoint k) ∧
      (∀ p i k, 1 ≤ k → ∀ y ∈ ((parameterLocalProductFamily A B).chart p).target,
        ((parameterLocalProductFamily A B).chart p).symm y ∈ tsupport (chi i) →
        ‖iteratedFDeriv ℝ k ((parameterLocalProductFamily A B).chart i ∘
          ((parameterLocalProductFamily A B).chart p).symm) y‖ ≤ max (TP k) (TS k)) := by
  obtain ⟨BS,hBS,hS⟩ := round3Outer_exists_uniform_prepared_tensor_cutoffs (E := Es) (X := M) BS₀ TS hBS₀ hTS Ds
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
  · exact round3Outer_tensorLocalProductCutoff_jet_bound A B hA hB _ _ hSs hPs BS BP hBS hBP hSj
      (fun p i k y hy _ => hPj p i k y hy)
  · exact round3Outer_tensorLocalProductTransition_jet_bound A B hA hB _ _ hSsupp hPsupp TS TP
      (fun p i k hk y hy hi => RS.transition_jets p i k hk y hy
        (squareNormalizedCutoff_tsupport_subset RS.raw i hi))
      (fun p i k hk y hy hi => RP.transition_jets p i k hk y hy
        (tensorLocalNormalizedCutoff_tsupport_subset RP.raw i hi))


end GlobalEmbedding.Offline

#print axioms GlobalEmbedding.Offline.round3Outer_exists_uniform_local_product_smoothing_providers
