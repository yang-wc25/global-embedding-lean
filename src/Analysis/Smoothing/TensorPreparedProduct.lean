import Smoothing.TensorProductPreparation

/-!
# Uniform joint smoothing data from the actual two raw preparations

The raw record below contains only original bump, chart and enlarged-support
data. In particular it contains no normalized cutoff, smoothed field or output
estimate. Normalization, joint smoothness, the square partition, all derivative
profiles and the actual support multiplicity are proved here for one explicit
product family. Constants are selected before either finite atlas.

Constructing the raw geometric preparation on the original compact parameter
evaluation neighborhood remains a separate geometric obligation; this module
does not replace that obligation by a claimed construction on arbitrary P.
-/

open Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Continuation Function Set
open scoped ContDiff Topology BigOperators

namespace GlobalEmbedding.Offline

noncomputable section
set_option backward.isDefEq.respectTransparency false

section Raw

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℝ, E) ∞ X]

/-- The graph used by normalization is exactly the original atlas graph. -/
theorem tensorEnlargedSupportGraph_eq_original (A : BufferedAtlas X E) :
    tensorEnlargedSupportGraph A.support = A.supportGraph := by
  ext i j
  rfl

/-- Original Setup 6 maximum support degree controls every actual vertex. -/
theorem tensorSupportDegree_le_original (A : BufferedAtlas X E) (i : Fin A.count) :
    tensorEnlargedSupportDegree A.support i ≤ A.supportDegree := by
  classical
  unfold tensorEnlargedSupportDegree
  rw [tensorEnlargedSupportGraph_eq_original]
  exact Finset.le_sup (f := fun j : Fin A.count => A.supportGraph.degree j) (Finset.mem_univ i)

/-- Only genuine fixed raw geometric preparation is stored. The derivative
profiles refer to actual functions, and the degree is the ORIGINAL graph. -/
structure TensorRawCutoffPreparation (A : BufferedAtlas X E) (B₀ T : ℕ → ℝ) (D : ℕ) where
  raw : Fin A.count → X → ℝ
  smooth : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (raw i)
  plateau_cover : ∀ x, ∃ i, raw i x = 1
  inner_support : ∀ i, tsupport (raw i) ⊆ A.inner i
  enlarged_support : ∀ i, tsupport (raw i) ⊆ A.support i
  degree : A.supportDegree ≤ D
  own_jets : ∀ i k, ∀ y ∈ (A.chart i).target,
    ‖iteratedFDeriv ℝ k (raw i ∘ (A.chart i).symm) y‖ ≤ B₀ k
  transition_jets : ∀ p i k, 1 ≤ k → ∀ y ∈ (A.chart p).target,
    (A.chart p).symm y ∈ tsupport (raw i) →
    ‖iteratedFDeriv ℝ k (A.chart i ∘ (A.chart p).symm) y‖ ≤ T k

/-- The actual raw preparation supplies each normalized provider, uniformly
before the atlas is chosen. -/
theorem exists_uniform_prepared_tensor_cutoffs
    (B₀ T : ℕ → ℝ) (hB₀ : ∀ j, 0 ≤ B₀ j) (hT : ∀ j, 0 ≤ T j) (D : ℕ) :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧
      ∀ (A : BufferedAtlas X E) (hA : IsSmoothBufferedAtlas A)
        (R : TensorRawCutoffPreparation A B₀ T D),
      let chi := squareNormalizedCutoff R.raw
      (∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i)) ∧
      (∀ x, ∑ i, chi i x ^ 2 = 1) ∧
      (∀ i, tsupport (chi i) ⊆ A.inner i) ∧
      (∀ x, (activeCutoffIndices chi x).card ≤ D + 1) ∧
      (∀ p i j, ∀ y ∈ bufferedInnerCoordinates A p,
        (A.chart p).symm y ∈ tsupport (chi i) →
        ‖iteratedFDeriv ℝ j (chi i ∘ (A.chart p).symm) y‖ ≤ B j) := by
  obtain ⟨B, hB, h⟩ := exists_uniform_tensor_cutoff_provider
    (E := E) (M := X) B₀ T hB₀ hT D
  refine ⟨B, hB, fun A hA R => ?_⟩
  exact h A hA R.raw R.smooth R.plateau_cover R.inner_support A.support R.enlarged_support
    (fun i => (tensorSupportDegree_le_original A i).trans R.degree) R.own_jets R.transition_jets

end Raw

variable {Ep Es P M : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Es] [NormedSpace ℝ Es]
  [TopologicalSpace P] [TopologicalSpace M]
  [ChartedSpace Ep P] [IsManifold 𝓘(ℝ, Ep) ∞ P]
  [ChartedSpace Es M] [IsManifold 𝓘(ℝ, Es) ∞ M]

local instance : ChartedSpace (Ep × Es) (P × M) := prodChartedSpace Ep P Es M
local instance : IsManifold 𝓘(ℝ, Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Ep)) (I' := 𝓘(ℝ, Es)) (n := ∞) P M

/-- ALL true joint smoothing geometry from the two original raw preparations.
The same explicit chi, B and T feed both the map and native tensor endpoints.
The only degree factor is `(Dp+1)*(Ds+1)`, independent of both chart counts. -/
theorem exists_uniform_prepared_product_smoothing_providers
    (BS₀ TS BP₀ TP : ℕ → ℝ)
    (hBS₀ : ∀ j, 0 ≤ BS₀ j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP₀ : ∀ j, 0 ≤ BP₀ j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ) :
    ∃ Bjoint : ℕ → ℝ, (∀ j, 0 ≤ Bjoint j) ∧
      ∀ (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
        (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
        (RS : TensorRawCutoffPreparation A BS₀ TS Ds)
        (RP : TensorRawCutoffPreparation B BP₀ TP Dp),
      let chi := tensorProductCutoff A B (squareNormalizedCutoff RS.raw) (squareNormalizedCutoff RP.raw)
      (∀ i, ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, ℝ) ∞ (chi i)) ∧
      (∀ z, ∑ i, chi i z ^ 2 = 1) ∧
      (∀ i, tsupport (chi i) ⊆ (parameterProductAtlas A B).inner i) ∧
      (∀ z, (activeCutoffIndices chi z).card ≤ (Dp + 1) * (Ds + 1)) ∧
      (∀ p i k, ∀ y ∈ bufferedInnerCoordinates (parameterProductAtlas A B) p,
        ((parameterProductAtlas A B).chart p).symm y ∈ tsupport (chi i) →
        ‖iteratedFDeriv ℝ k (chi i ∘ ((parameterProductAtlas A B).chart p).symm) y‖ ≤ Bjoint k) ∧
      (∀ p i k, 1 ≤ k → ∀ y ∈ bufferedInnerCoordinates (parameterProductAtlas A B) p,
        ((parameterProductAtlas A B).chart p).symm y ∈ tsupport (chi i) →
        ‖iteratedFDeriv ℝ k ((parameterProductAtlas A B).chart i ∘
          ((parameterProductAtlas A B).chart p).symm) y‖ ≤ max (TP k) (TS k)) := by
  obtain ⟨BS, hBS, hS⟩ := exists_uniform_prepared_tensor_cutoffs
    (E := Es) (X := M) BS₀ TS hBS₀ hTS Ds
  obtain ⟨BP, hBP, hP⟩ := exists_uniform_prepared_tensor_cutoffs
    (E := Ep) (X := P) BP₀ TP hBP₀ hTP Dp
  refine ⟨tensorProductJetConstant BP BS, tensorProductJetConstant_nonneg hBP hBS, ?_⟩
  intro A B hA hB RS RP
  obtain ⟨hSs, hSpart, hSsupp, hSD, hSjet⟩ := hS A hA RS
  obtain ⟨hPs, hPpart, hPsupp, hPD, hPjet⟩ := hP B hB RP
  exact ⟨tensorProductCutoff_contMDiff A B _ _ hSs hPs,
    tensorProductCutoff_square_sum A B _ _ hSpart hPpart,
    tensorProductCutoff_support A B _ _ hSsupp hPsupp,
    tensorProductCutoff_card_le A B _ _ (Ds + 1) (Dp + 1) hSD hPD,
    tensorProductCutoff_jet_bound A B hA hB _ _ hSs hPs BS BP hBS hBP hSjet hPjet,
    tensorProductTransition_jet_bound A B hA hB _ _ hSsupp hPsupp TS TP
      (fun p i k hk y hy hi => RS.transition_jets p i k hk y hy.1
        (squareNormalizedCutoff_tsupport_subset RS.raw i hi))
      (fun p i k hk y hy hi => RP.transition_jets p i k hk y hy.1
        (squareNormalizedCutoff_tsupport_subset RP.raw i hi))⟩

end
end GlobalEmbedding.Offline
