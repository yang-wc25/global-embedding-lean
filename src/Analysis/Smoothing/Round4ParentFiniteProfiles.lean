import Smoothing.Round4TensorFiniteProviders
import Smoothing.Round3ParameterCompactParents
import Probes.Round3ParameterNativeParent

/-! Actual product parents have a named joint derivative profile. It reads
only the raw source/parameter cutoff and transition prefixes through j.
The statement applies in every receiving chart and retains the exact supported
parameter pullback used by the whole primary packet. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set Filter Manifold IsManifold
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

def round4ParentProfile (BS TS BP TP : ℕ → ℝ) (Ds Dp : ℕ) : ℕ → ℝ :=
  let C := round4ProductCutoffProfile BS TS BP TP Ds Dp
  tensorProductJetConstant C C

theorem round4ParentProfile_nonneg
    {BS TS BP TP : ℕ → ℝ}
    (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp j : ℕ) :
    0 ≤ round4ParentProfile BS TS BP TP Ds Dp j :=
  tensorProductJetConstant_nonneg
    (round4ProductCutoffProfile_nonneg hBS hTS hBP hTP Ds Dp)
    (round4ProductCutoffProfile_nonneg hBS hTS hBP hTP Ds Dp) j

theorem round4ParentProfile_congr_prefix (Ds Dp j : ℕ)
    {BS₁ BS₂ TS₁ TS₂ BP₁ BP₂ TP₁ TP₂ : ℕ → ℝ}
    (hBS : ∀ a ≤ j, BS₁ a = BS₂ a) (hTS : ∀ a ≤ j, TS₁ a = TS₂ a)
    (hBP : ∀ a ≤ j, BP₁ a = BP₂ a) (hTP : ∀ a ≤ j, TP₁ a = TP₂ a) :
    round4ParentProfile BS₁ TS₁ BP₁ TP₁ Ds Dp j =
      round4ParentProfile BS₂ TS₂ BP₂ TP₂ Ds Dp j := by
  have h (k : ℕ) (hk : k ≤ j) :
      round4ProductCutoffProfile BS₁ TS₁ BP₁ TP₁ Ds Dp k =
        round4ProductCutoffProfile BS₂ TS₂ BP₂ TP₂ Ds Dp k :=
    round4ProductCutoffProfile_congr_prefix Ds Dp k
      (fun a ha => hBS a (ha.trans hk)) (fun a ha => hTS a (ha.trans hk))
      (fun a ha => hBP a (ha.trans hk)) (fun a ha => hTP a (ha.trans hk))
  exact parameterTensorProductConstant_congr_prefix j h h

variable {n d c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × Es
private local instance : ChartedSpace X (P × M) := prodChartedSpace Ep P Es M
private local instance : IsManifold 𝓘(ℝ,X) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,Es)) (n := ∞) P M

theorem round4_actual_product_parent_jets
    (BS TS BP TP : ℕ → ℝ)
    (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin c) P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (K : Set P) (RS : TensorRawCutoffPreparation A BS TS Ds)
    (RP : TensorLocalRawPreparation B K BP TP Dp)
    (p i : Fin A.count × Fin c) (j : ℕ) (ell : ℝ) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (y : X) (hy : y ∈ ((parameterLocalProductFamily A B).chart p).target) :
    ell^j*‖iteratedFDeriv ℝ j
      (round3ParameterProductParent A B (squareNormalizedCutoff RS.raw)
        (tensorLocalNormalizedCutoff RP.raw) i ∘ ((parameterLocalProductFamily A B).chart p).symm) y‖ ≤
      round4ParentProfile BS TS BP TP Ds Dp j := by
  let chi := parameterLocalProductCutoff A B (squareNormalizedCutoff RS.raw)
    (tensorLocalNormalizedCutoff RP.raw)
  let q := (parameterLocalProductFamily A B).chart p
  let C := round4ProductCutoffProfile BS TS BP TP Ds Dp
  have hC := round4ProductCutoffProfile_nonneg hBS hTS hBP hTP Ds Dp
  obtain ⟨W,hW,hKW,hchi,hPart,hSupport,hCount,hJets,hTransition⟩ :=
    round4_actual_product_smoothing_providers BS TS BP TP hBS hTS hBP hTP Ds Dp
      c A B hA hB K RS RP
  let : ChartedSpace X X := chartedSpaceSelf X
  have hf : ContDiffOn ℝ ∞ (chi i ∘ q.symm) q.target :=
    ((hchi i).comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas
      (parameterLocalProductFamily_chart_mem A B hA hB p))).contDiffOn
  have hj (k : ℕ) : ‖iteratedFDeriv ℝ k (chi i ∘ q.symm) y‖ ≤ C k := by
    by_cases hs : q.symm y ∈ tsupport (chi i)
    · exact hJets p i k y hy hs
    · rw [iteratedFDeriv_comp_eq_zero_off_tsupport _ q.symm y (q.symm.continuousAt hy) hs k,norm_zero]
      exact hC k
  have hb := tensor_scalar_product_jet_le C C hC hC q.open_target hf hf hy j hj hj
  change ‖iteratedFDeriv ℝ j
    (round3ParameterProductParent A B (squareNormalizedCutoff RS.raw)
      (tensorLocalNormalizedCutoff RP.raw) i ∘ q.symm) y‖ ≤ round4ParentProfile BS TS BP TP Ds Dp j at hb
  exact (mul_le_mul_of_nonneg_left hb (pow_nonneg hell j)).trans
    (mul_le_of_le_one_left (round4ParentProfile_nonneg hBS hTS hBP hTP Ds Dp j)
      (pow_le_one₀ hell hell1))

#print axioms round4_actual_product_parent_jets
#print axioms round4ParentProfile_congr_prefix
end GlobalEmbedding.Continuation
