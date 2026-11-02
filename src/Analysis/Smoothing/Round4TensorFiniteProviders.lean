import Smoothing.Round4LocalNormalizationFiniteBounds
import Smoothing.Round3OuterProviders

/-!
# Original raw preparations produce explicit finite smoothing geometry

These providers preserve the original source and parameter raw functions,
their exact normalizations and the receiving-chart domains. At order j the
constructed joint cutoff profile reads only raw B and transition T through j.
The local multiplicity remains (Ds+1)*(Dp+1), independent of both chart counts.
-/

open GlobalEmbedding.Offline GlobalEmbedding.Paper Function Set Filter Manifold IsManifold
open scoped ContDiff Topology BigOperators

namespace GlobalEmbedding.Continuation
noncomputable section
set_option backward.isDefEq.respectTransparency false

def round4SourceCutoffProfile (B T : ℕ → ℝ) (D : ℕ) : ℕ → ℝ :=
  round4NormalizationProfile (round4ChartTransferProfile B T)
    (round4SquareSumProfile (D+1) (round4ChartTransferProfile B T))

def round4ParameterCutoffProfile (B T : ℕ → ℝ) (D : ℕ) : ℕ → ℝ :=
  round4LocalNormalizationProfile (round4ChartTransferProfile B T) (D+1)

theorem round4SourceCutoffProfile_nonneg {B T : ℕ → ℝ}
    (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (D j : ℕ) :
    0 ≤ round4SourceCutoffProfile B T D j :=
  round4NormalizationProfile_nonneg (round4ChartTransferProfile_nonneg hB hT)
    (round4SquareSumProfile_nonneg _ (round4ChartTransferProfile_nonneg hB hT)) j

theorem round4ParameterCutoffProfile_nonneg {B T : ℕ → ℝ}
    (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (D j : ℕ) :
    0 ≤ round4ParameterCutoffProfile B T D j :=
  round4LocalNormalizationProfile_nonneg (round4ChartTransferProfile_nonneg hB hT) (D+1) j

theorem round4SourceCutoffProfile_congr_prefix {B₁ B₂ T₁ T₂ : ℕ → ℝ} (D j : ℕ)
    (hB : ∀ a ≤ j, B₁ a = B₂ a) (hT : ∀ a ≤ j, T₁ a = T₂ a) :
    round4SourceCutoffProfile B₁ T₁ D j = round4SourceCutoffProfile B₂ T₂ D j := by
  have hL (a : ℕ) (ha : a ≤ j) :
      round4ChartTransferProfile B₁ T₁ a = round4ChartTransferProfile B₂ T₂ a :=
    round4ChartTransferProfile_congr_prefix a (fun k hk => hB k (hk.trans ha))
      (fun k hk => hT k (hk.trans ha))
  exact round4NormalizationProfile_congr_prefix j hL
    (fun a ha => round4SquareSumProfile_congr_prefix (D+1) a (fun k hk => hL k (hk.trans ha)))

theorem round4ParameterCutoffProfile_congr_prefix {B₁ B₂ T₁ T₂ : ℕ → ℝ} (D j : ℕ)
    (hB : ∀ a ≤ j, B₁ a = B₂ a) (hT : ∀ a ≤ j, T₁ a = T₂ a) :
    round4ParameterCutoffProfile B₁ T₁ D j = round4ParameterCutoffProfile B₂ T₂ D j := by
  apply round4LocalNormalizationProfile_congr_prefix (D+1) j
  intro a ha
  exact round4ChartTransferProfile_congr_prefix a (fun k hk => hB k (hk.trans ha))
    (fun k hk => hT k (hk.trans ha))

section OneFactor
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℝ,E) ∞ X]

/-- Every receiving chart sees the actual source normalization with the
explicit finite cost. The cutoff need not be active at the evaluation point. -/
theorem round4_prepared_source_cutoff_jets
    (B₀ T : ℕ → ℝ) (hB₀ : ∀ j, 0 ≤ B₀ j) (hT : ∀ j, 0 ≤ T j) (D : ℕ)
    (A : BufferedAtlas X E) (hA : IsSmoothBufferedAtlas A)
    (R : TensorRawCutoffPreparation A B₀ T D) :
    ∀ p i j, ∀ y ∈ (A.chart p).target,
      ‖iteratedFDeriv ℝ j (squareNormalizedCutoff R.raw i ∘ (A.chart p).symm) y‖ ≤
        round4SourceCutoffProfile B₀ T D j := by
  let L := round4ChartTransferProfile B₀ T
  have hL : ∀ j, 0 ≤ L j := round4ChartTransferProfile_nonneg hB₀ hT
  have hD := activeCutoffIndices_card_le_enlarged_degree A.support R.raw R.enlarged_support D
    (fun i => (tensorSupportDegree_le_original A i).trans R.degree)
  intro p
  let c := (A.chart p).symm
  let O := (A.chart p).target
  have hO : IsOpen O := (A.chart p).open_target
  have hb (i : Fin A.count) : ContDiffOn ℝ ∞ (R.raw i ∘ c) O :=
    ((R.smooth i).comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem p))).contDiffOn
  have hc (y : E) (hy : y ∈ O) : ContinuousAt c y := (A.chart p).symm.continuousAt hy
  have hactive (i : Fin A.count) (y : E) (hy : y ∈ O)
      (hi : c y ∈ tsupport (R.raw i)) (j : ℕ) :
      ‖iteratedFDeriv ℝ j (R.raw i ∘ c) y‖ ≤ L j := by
    have his := A.inner_subset i (R.inner_support i hi)
    exact round4_actual_chart_pullback_jet_bound B₀ T hB₀ hT _ (R.smooth i)
      (A.chart p) (A.chart i) (hA.chart_mem p) (hA.chart_mem i) y ⟨hy,his⟩
      (fun k => R.own_jets i k _ ((A.chart i).map_source his))
      (fun k hk => R.transition_jets p i k hk y hy hi) j
  have hall (i : Fin A.count) (j : ℕ) (y : E) (hy : y ∈ O) :
      ‖iteratedFDeriv ℝ j (R.raw i ∘ c) y‖ ≤ L j := by
    by_cases hi : c y ∈ tsupport (R.raw i)
    · exact hactive i y hy hi j
    · rw [iteratedFDeriv_comp_eq_zero_off_tsupport _ c y (hc y hy) hi j,norm_zero]
      exact hL j
  have hsum (j : ℕ) (y : E) (hy : y ∈ O) :
      ‖iteratedFDeriv ℝ j (squareCutoffSum (fun i => R.raw i ∘ c)) y‖ ≤
        round4SquareSumProfile (D+1) L j :=
    round4_square_sum_jet_bound L hL (D+1) R.raw c O hO hb y hy (hc y hy)
      (hD (c y)) (fun i hi => hactive i y hy hi) j
  intro i j y hy
  exact round4_normalized_cutoff_jet_bound L (round4SquareSumProfile (D+1) L) hL
    (round4SquareSumProfile_nonneg _ hL) (fun a => R.raw a ∘ c) O hO hb
    (fun z _ => one_le_squareCutoffSum_of_plateau R.raw (c z) (R.plateau_cover (c z)))
    hsum i (hall i) j y hy

/-- The same finite computation for parameter plateaus covering only Q. -/
theorem round4_prepared_parameter_cutoff_jets
    (B₀ T : ℕ → ℝ) (hB₀ : ∀ j, 0 ≤ B₀ j) (hT : ∀ j, 0 ≤ T j) (D : ℕ)
    {ι : Type*} [Fintype ι] (A : TensorBufferedChartFamily ι X E)
    (hA : ∀ i, A.chart i ∈ maximalAtlas 𝓘(ℝ,E) ∞ X)
    (Q : Set X) (R : TensorLocalRawPreparation A Q B₀ T D) :
    ∀ p i j, ∀ y ∈ (A.chart p).target,
      ‖iteratedFDeriv ℝ j (tensorLocalNormalizedCutoff R.raw i ∘ (A.chart p).symm) y‖ ≤
        round4ParameterCutoffProfile B₀ T D j := by
  let L := round4ChartTransferProfile B₀ T
  have hL : ∀ j, 0 ≤ L j := round4ChartTransferProfile_nonneg hB₀ hT
  have hD := activeCutoffIndices_card_le_enlarged_degree R.enlarged R.raw R.enlarged_support D R.degree
  intro p i j y hy
  apply round4_local_normalized_cutoff_jet_bound L hL (D+1) R.raw (A.chart p).symm
    (A.chart p).target (A.chart p).open_target
    (fun a => ((R.smooth a).comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hA p))).contDiffOn)
    (A.chart p).symm.continuousOn (fun z _ => hD _) ?_ i j y hy
  intro a z hz ha k
  have has := A.inner_subset a (R.inner_support a ha)
  exact round4_actual_chart_pullback_jet_bound B₀ T hB₀ hT _ (R.smooth a)
    (A.chart p) (A.chart a) (hA p) (hA a) z ⟨hz,has⟩
    (fun l => R.own_jets a l _ ((A.chart a).map_source has))
    (fun l hl => R.transition_jets p a l hl z hz ha) k

end OneFactor

def round4ProductCutoffProfile (BS₀ TS BP₀ TP : ℕ → ℝ) (Ds Dp : ℕ) : ℕ → ℝ :=
  tensorProductJetConstant (round4ParameterCutoffProfile BP₀ TP Dp)
    (round4SourceCutoffProfile BS₀ TS Ds)

theorem round4ProductCutoffProfile_nonneg {BS₀ TS BP₀ TP : ℕ → ℝ}
    (hBS₀ : ∀ j, 0 ≤ BS₀ j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP₀ : ∀ j, 0 ≤ BP₀ j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp j : ℕ) :
    0 ≤ round4ProductCutoffProfile BS₀ TS BP₀ TP Ds Dp j :=
  tensorProductJetConstant_nonneg (round4ParameterCutoffProfile_nonneg hBP₀ hTP Dp)
    (round4SourceCutoffProfile_nonneg hBS₀ hTS Ds) j

theorem round4ProductCutoffProfile_congr_prefix
    {BS₁ BS₂ TS₁ TS₂ BP₁ BP₂ TP₁ TP₂ : ℕ → ℝ} (Ds Dp j : ℕ)
    (hBS : ∀ a ≤ j, BS₁ a = BS₂ a) (hTS : ∀ a ≤ j, TS₁ a = TS₂ a)
    (hBP : ∀ a ≤ j, BP₁ a = BP₂ a) (hTP : ∀ a ≤ j, TP₁ a = TP₂ a) :
    round4ProductCutoffProfile BS₁ TS₁ BP₁ TP₁ Ds Dp j =
      round4ProductCutoffProfile BS₂ TS₂ BP₂ TP₂ Ds Dp j := by
  apply parameterTensorProductConstant_congr_prefix j
  · intro a ha
    exact round4ParameterCutoffProfile_congr_prefix Dp a
      (fun k hk => hBP k (hk.trans ha)) (fun k hk => hTP k (hk.trans ha))
  · intro a ha
    exact round4SourceCutoffProfile_congr_prefix Ds a
      (fun k hk => hBS k (hk.trans ha)) (fun k hk => hTS k (hk.trans ha))

section Product
variable {Ep Es P M : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Es] [NormedSpace ℝ Es]
  [TopologicalSpace P] [TopologicalSpace M]
  [ChartedSpace Ep P] [IsManifold 𝓘(ℝ,Ep) ∞ P]
  [ChartedSpace Es M] [IsManifold 𝓘(ℝ,Es) ∞ M]
  [MeasurableSpace Ep] [BorelSpace Ep] [FiniteDimensional ℝ Ep]

local instance : ChartedSpace (Ep × Es) (P × M) := prodChartedSpace Ep P Es M
local instance : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,Es)) (n := ∞) P M

/-- Complete real product smoothing geometry with the explicit finite raw
profile. This is directly usable by both the map and source-tensor estimates. -/
theorem round4_actual_product_smoothing_providers
    (BS₀ TS BP₀ TP : ℕ → ℝ)
    (hBS₀ : ∀ j, 0 ≤ BS₀ j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP₀ : ∀ j, 0 ≤ BP₀ j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (pcount : ℕ) (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ j, B.chart j ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (Q : Set P) (RS : TensorRawCutoffPreparation A BS₀ TS Ds)
    (RP : TensorLocalRawPreparation B Q BP₀ TP Dp) :
    let chi := parameterLocalProductCutoff A B
      (squareNormalizedCutoff RS.raw) (tensorLocalNormalizedCutoff RP.raw)
    ∃ W : Set P, IsOpen W ∧ Q ⊆ W ∧
      (∀ i, ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,ℝ) ∞ (chi i)) ∧
      (∀ z : P × M, z.1 ∈ W → ∑ i, chi i z^2 = 1) ∧
      (∀ i, tsupport (chi i) ⊆ (parameterLocalProductFamily A B).inner i) ∧
      (∀ z, (activeCutoffIndices chi z).card ≤ (Ds+1)*(Dp+1)) ∧
      (∀ p i k, ∀ y ∈ ((parameterLocalProductFamily A B).chart p).target,
        ((parameterLocalProductFamily A B).chart p).symm y ∈ tsupport (chi i) →
        ‖iteratedFDeriv ℝ k (chi i ∘ ((parameterLocalProductFamily A B).chart p).symm) y‖ ≤
          round4ProductCutoffProfile BS₀ TS BP₀ TP Ds Dp k) ∧
      (∀ p i k, 1 ≤ k → ∀ y ∈ ((parameterLocalProductFamily A B).chart p).target,
        ((parameterLocalProductFamily A B).chart p).symm y ∈ tsupport (chi i) →
        ‖iteratedFDeriv ℝ k ((parameterLocalProductFamily A B).chart i ∘
          ((parameterLocalProductFamily A B).chart p).symm) y‖ ≤ max (TP k) (TS k)) := by
  have hpos (x : M) := one_le_squareCutoffSum_of_plateau RS.raw x (RS.plateau_cover x)
  have hSs := squareNormalizedCutoff_contMDiff RS.raw RS.smooth hpos
  have hSpart (x : M) := squareNormalizedCutoff_sum_sq RS.raw x (zero_lt_one.trans_le (hpos x))
  have hSsupp (i : Fin A.count) :=
    (squareNormalizedCutoff_tsupport_subset RS.raw i).trans (RS.inner_support i)
  have hSD := squareNormalizedCutoff_card_le_enlarged_degree A.support RS.raw RS.enlarged_support Ds
    (fun i => (tensorSupportDegree_le_original A i).trans RS.degree)
  have hPD := activeCutoffIndices_card_le_enlarged_degree RP.enlarged RP.raw RP.enlarged_support Dp RP.degree
  have hPs := tensorLocalNormalizedCutoff_contMDiff RP.raw RP.smooth
  have hPsupp (i : Fin pcount) :=
    (tensorLocalNormalizedCutoff_tsupport_subset RP.raw i).trans (RP.inner_support i)
  obtain ⟨W,hW,hQW,hchi,hpart,hsupp,hD⟩ := parameterLocalProductCutoff_preparation_near A B
    (squareNormalizedCutoff RS.raw) RP.raw hSs RP.smooth hSpart hSsupp RP.inner_support
    (Ds+1) (Dp+1) hSD hPD Q RP.plateau_on
  refine ⟨W,hW,hQW,hchi,hpart,hsupp,hD,?_,?_⟩
  · exact round3Outer_tensorLocalProductCutoff_jet_bound A B hA hB _ _ hSs hPs
      (round4SourceCutoffProfile BS₀ TS Ds) (round4ParameterCutoffProfile BP₀ TP Dp)
      (round4SourceCutoffProfile_nonneg hBS₀ hTS Ds) (round4ParameterCutoffProfile_nonneg hBP₀ hTP Dp)
      (fun p i k y hy _ => round4_prepared_source_cutoff_jets BS₀ TS hBS₀ hTS Ds A hA RS p i k y hy)
      (fun p i k y hy _ => round4_prepared_parameter_cutoff_jets BP₀ TP hBP₀ hTP Dp B hB Q RP p i k y hy)
  · exact round3Outer_tensorLocalProductTransition_jet_bound A B hA hB _ _ hSsupp hPsupp TS TP
      (fun p i k hk y hy hi => RS.transition_jets p i k hk y hy
        (squareNormalizedCutoff_tsupport_subset RS.raw i hi))
      (fun p i k hk y hy hi => RP.transition_jets p i k hk y hy
        (tensorLocalNormalizedCutoff_tsupport_subset RP.raw i hi))
end Product

#print axioms round4_prepared_source_cutoff_jets
#print axioms round4_prepared_parameter_cutoff_jets
#print axioms round4_actual_product_smoothing_providers
#print axioms round4ProductCutoffProfile_congr_prefix
end
end GlobalEmbedding.Continuation
