import Smoothing.Round4PreparedPairFiniteGeometry
import Smoothing.ParameterRound2CompactPair

/-!
# Same-domain original (6.4) and gain with a finite raw-geometry constant

This is the actual closed-parameter pair consumed by repair. Finiteness comes
from the same compact original Ω/Q norm domains on input and output. The
constant is a named finite expression and is independent of both chart counts,
all raw functions, both fields and the scales. Its raw derivative depth is
proved to be m+2, independently of the kernel moment order r.
-/

open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set MeasureTheory Manifold IsManifold
open scoped ContDiff Topology ENNReal BigOperators
namespace GlobalEmbedding.Continuation
noncomputable section

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]

local instance round4LocalSetPairChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance round4LocalSetPairIsManifold : IsManifold
    𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) P M

local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ey" => EuclideanSpace ℝ (Fin N)

def round4PreparedPairConstant (n d : ℕ) (rho : ℝ) (hrho : 0 < rho)
    (BS₀ TS BP₀ TP : ℕ → ℝ) (Ds Dp m r : ℕ) : ℝ :=
  max (round4PreparedPairTailConstant n d rho hrho BS₀ TS BP₀ TP Ds Dp m r)
    (round4PreparedPairGainConstant n d rho hrho BS₀ TS BP₀ TP Ds Dp m r)

/-- The actual single pair constant reads raw geometry only through m+2. -/
theorem round4PreparedPairConstant_congr_prefix
    (n d : ℕ) (rho : ℝ) (hrho : 0 < rho) (Ds Dp m r : ℕ)
    {BS₁ BS₂ TS₁ TS₂ BP₁ BP₂ TP₁ TP₂ : ℕ → ℝ}
    (hBS : ∀ a ≤ m+2, BS₁ a = BS₂ a) (hTS : ∀ a ≤ m+2, TS₁ a = TS₂ a)
    (hBP : ∀ a ≤ m+2, BP₁ a = BP₂ a) (hTP : ∀ a ≤ m+2, TP₁ a = TP₂ a) :
    round4PreparedPairConstant n d rho hrho BS₁ TS₁ BP₁ TP₁ Ds Dp m r =
      round4PreparedPairConstant n d rho hrho BS₂ TS₂ BP₂ TP₂ Ds Dp m r := by
  unfold round4PreparedPairConstant
  rw [round4PreparedPairTailConstant_congr_prefix n d rho hrho Ds Dp m r hBS hTS hBP hTP,
    round4PreparedPairGainConstant_congr_prefix n d rho hrho Ds Dp m r hBS hTS hBP hTP]

theorem round4_actual_local_set_pair_smoothing
    (BS₀ TS BP₀ TP : ℕ → ℝ)
    (hBS₀ : ∀ j, 0 ≤ BS₀ j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP₀ : ∀ j, 0 ≤ BP₀ j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (rho : ℝ) (hrho : 0 < rho) (m r : ℕ) :
    let C := round4PreparedPairConstant n d rho hrho BS₀ TS BP₀ TP Ds Dp m r
    0 ≤ C ∧
      ∀ (pcount : ℕ) (A : BufferedAtlas M Es)
        (B : TensorBufferedChartFamily (Fin pcount) P Ep)
        (hA : IsSmoothBufferedAtlas A)
        (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ, Ep) ∞ P)
        (parameterSet : Set P)
        (RS : TensorRawCutoffPreparation A BS₀ TS Ds)
        (RP : TensorLocalRawPreparation B parameterSet BP₀ TP Dp),
      rho ≤ min B.buffer A.buffer →
      ∀ (Omega : Fin A.count → Set Es) (Q : Fin pcount → Set Ep),
      (∀ i, IsCompact (Omega i)) → (∀ i, IsCompact (Q i)) →
      (∀ i, Omega i ⊆ (A.chart i).target) → (∀ i, Q i ⊆ (B.chart i).target) →
      (∀ i, bufferedSamplingCoordinates A i ⊆ Omega i) →
      (∀ i, tensorLocalSamplingCoordinates B i ⊆ Q i) →
      ∀ (S : Fin A.count × Fin pcount → Set (Fin (n+d) → ℝ)),
      (∀ i, S i ⊆ round3OuterOriginalEvaluation A B parameterSet i) →
      ∀ tau ell t : ℝ, 0 < tau → tau ≤ ell → ell ≤ t → t ≤ 1 →
      ∀ (u : P × M → Ey),
      (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B.chart u i)
        (incrementsOriginalDifferentiation A B.chart i)) →
      ∀ (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, Es) x)),
      (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart H i)
        (incrementsOriginalDifferentiation A B.chart i)) →
      ∀ budget : ℝ,
      (parameterLocalOriginalTotalPairWeighted A B u H r t
        (incrementsOriginalEvaluation A B.chart Omega Q univ)).toReal ≤ budget →
      let mu := (volume : Measure (Ep × Es))
      let K := fixedSmoothingKernel mu rho hrho r
      let chi := parameterLocalProductCutoff A B
        (squareNormalizedCutoff RS.raw) (tensorLocalNormalizedCutoff RP.raw)
      let SF := parameterLocalMapSmoothing (parameterLocalProductFamily A B) mu K ell chi u
      let SH := tensorLocalParameterSmoothing A B hA mu K ell chi H
      ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ SF ∧
      (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart SH i)
        (incrementsOriginalDifferentiation A B.chart i)) ∧
      parameterLocalOriginalTotalPairWeighted A B
        (fun z => u z - SF z) (fun p x => H p x - SH p x)
        m tau S ≠ ⊤ ∧
      (parameterLocalOriginalTotalPairWeighted A B
        (fun z => u z - SF z) (fun p x => H p x - SH p x)
        m tau S).toReal ≤
        C * (budget * (ell/t)^r +
          (parameterLocalOriginalTotalPairWeighted A B u H m t
            (incrementsOriginalEvaluation A B.chart Omega Q univ)).toReal * (tau/t)^r) ∧
      parameterLocalOriginalTotalPairWeighted A B SF SH
        m tau S ≠ ⊤ ∧
      (parameterLocalOriginalTotalPairWeighted A B SF SH
        m tau S).toReal ≤ C * budget := by
  let Ct := round4PreparedPairTailConstant n d rho hrho BS₀ TS BP₀ TP Ds Dp m r
  let Cg := round4PreparedPairGainConstant n d rho hrho BS₀ TS BP₀ TP Ds Dp m r
  obtain ⟨hCt, htail⟩ := round4_prepared_original_pair_tail
    (n := n) (d := d) (q := N) (M := M) (P := P)
    BS₀ TS BP₀ TP hBS₀ hTS hBP₀ hTP Ds Dp rho hrho m r
  obtain ⟨hCg, hgain⟩ := round4_prepared_original_pair_gain
    (n := n) (d := d) (q := N) (M := M) (P := P)
    BS₀ TS BP₀ TP hBS₀ hTS hBP₀ hTP Ds Dp rho hrho m r
  refine ⟨hCt.trans (le_max_left _ _), ?_⟩
  intro pcount A B hA hB parameterSet RS RP hbuffer Omega Q hOmega hQ hOmegaTarget hQTarget
    hsource hparameter S hS tau ell t htau htaul helt ht1 u hu H hH budget hbudget
  have ht : 0 < t := htau.trans_le (htaul.trans helt)
  have hell : 0 < ell := htau.trans_le htaul
  have hbudget0 : 0 ≤ budget := ENNReal.toReal_nonneg.trans hbudget
  have hfull (j : ℕ) := parameterRound2_original_pair_on_compact_finite
    A B Omega Q hOmega hQ hOmegaTarget hQTarget u hu H hH j t
  have hdomains : ∀ i, tensorLocalOriginalSampling A B i ⊆
      incrementsOriginalEvaluation A B.chart Omega Q univ i := by
    intro i y hy
    exact ⟨hy.1, hsource i.1 hy.2.1, hparameter i.2 hy.2.2.1, Set.mem_univ _⟩
  have hle (j : ℕ) : parameterLocalOriginalTotalPairWeighted A B u H j t (tensorLocalOriginalSampling A B) ≤
      parameterLocalOriginalTotalPairWeighted A B u H j t
        (incrementsOriginalEvaluation A B.chart Omega Q univ) :=
    add_le_add (paperAtlasWeighted_mono_evaluation _ _ _ _ _ _ _ hdomains)
      (paperAtlasWeighted_mono_evaluation _ _ _ _ _ _ _ hdomains)
  have hsfinite (j : ℕ) := ne_top_of_le_ne_top (hfull j) (hle j)
  have hsle (j : ℕ) := ENNReal.toReal_mono (hfull j) (hle j)
  have hbase := add_le_add (parameterPaperAtlasCj_base_le_weighted 2 r t
      (incrementsOriginalMapCoordinates A B.chart u) (incrementsOriginalDifferentiation A B.chart)
        (tensorLocalOriginalSampling A B))
    (parameterPaperAtlasCj_base_le_weighted 0 r t
      (incrementsOriginalTensorCoordinates A B.chart H) (incrementsOriginalDifferentiation A B.chart)
        (tensorLocalOriginalSampling A B))
  have hbasefinite := ne_top_of_le_ne_top (hsfinite r) hbase
  have hbasebudget := (ENNReal.toReal_mono (hsfinite r) hbase).trans ((hsle r).trans hbudget)
  obtain ⟨W, hW, hUW, htailW⟩ := htail pcount A B hA hB parameterSet RS RP hbuffer
  have htresult := htailW tau ell t htau htaul helt ht1 u hu H hH
    (hsfinite r) (hsfinite m) budget ((hsle r).trans hbudget)
  have hgresult := hgain pcount A B hA hB parameterSet RS RP hbuffer
    tau ell hell (helt.trans ht1) htau.le htaul u hu H hH hbasefinite budget hbasebudget
  have hSW : ∀ i, S i ⊆ round3OuterOriginalEvaluation A B W i := by
    intro i y hy
    have hh := hS i hy
    exact ⟨hh.1,hUW hh.2⟩
  have hSuniv : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B.chart i := by
    intro i y hy
    have hh := hS i hy
    exact hh.1
  let mu := (volume : Measure (Ep × Es))
  let K := fixedSmoothingKernel mu rho hrho r
  let chi := parameterLocalProductCutoff A B
    (squareNormalizedCutoff RS.raw) (tensorLocalNormalizedCutoff RP.raw)
  let SF := parameterLocalMapSmoothing (parameterLocalProductFamily A B) mu K ell chi u
  let SH := tensorLocalParameterSmoothing A B hA mu K ell chi H
  have htailLe : parameterLocalOriginalTotalPairWeighted A B
      (fun z => u z-SF z) (fun p x => H p x-SH p x) m tau S ≤
      parameterLocalOriginalTotalPairWeighted A B
        (fun z => u z-SF z) (fun p x => H p x-SH p x) m tau (round3OuterOriginalEvaluation A B W) :=
    add_le_add (paperAtlasWeighted_mono_evaluation _ _ _ _ _ _ _ hSW)
      (paperAtlasWeighted_mono_evaluation _ _ _ _ _ _ _ hSW)
  have hgainLe : parameterLocalOriginalTotalPairWeighted A B SF SH m tau S ≤
      parameterLocalOriginalTotalPairWeighted A B SF SH m tau (incrementsOriginalDifferentiation A B.chart) :=
    add_le_add (paperAtlasWeighted_mono_evaluation _ _ _ _ _ _ _ hSuniv)
      (paperAtlasWeighted_mono_evaluation _ _ _ _ _ _ _ hSuniv)
  have htailFinite := ne_top_of_le_ne_top htresult.2.2.1 htailLe
  have htailBound := (ENNReal.toReal_mono htresult.2.2.1 htailLe).trans htresult.2.2.2
  have hgainFinite := ne_top_of_le_ne_top hgresult.2.2.1 hgainLe
  have hgainBound := (ENNReal.toReal_mono hgresult.2.2.1 hgainLe).trans hgresult.2.2.2
  refine ⟨htresult.1,htresult.2.1,htailFinite,?_,hgainFinite,?_⟩
  · refine htailBound.trans ?_
    have hratio0 : 0 ≤ (tau/t)^r := pow_nonneg (div_nonneg htau.le ht.le) _
    have hterm0 : 0 ≤ budget * (ell/t)^r +
        (parameterLocalOriginalTotalPairWeighted A B u H m t
          (incrementsOriginalEvaluation A B.chart Omega Q univ)).toReal * (tau/t)^r :=
      add_nonneg (mul_nonneg hbudget0 (pow_nonneg (div_nonneg hell.le ht.le) _))
        (mul_nonneg ENNReal.toReal_nonneg hratio0)
    exact (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right (hsle m) hratio0)) hCt).trans
      (mul_le_mul_of_nonneg_right (le_max_left Ct Cg) hterm0)
  · exact hgainBound.trans
      (mul_le_mul_of_nonneg_right (le_max_right Ct Cg) hbudget0)


theorem round4_actual_closed_parameter_same_domain_pair
    (BS₀ TS BP₀ TP : ℕ → ℝ)
    (hBS₀ : ∀ j, 0 ≤ BS₀ j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP₀ : ∀ j, 0 ≤ BP₀ j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (rho : ℝ) (hrho : 0 < rho) (m r : ℕ) :
    let C := round4PreparedPairConstant n d rho hrho BS₀ TS BP₀ TP Ds Dp m r
    0 ≤ C ∧
      ∀ (pcount : ℕ) (A : BufferedAtlas M Es)
        (B : TensorBufferedChartFamily (Fin pcount) P Ep)
        (hA : IsSmoothBufferedAtlas A)
        (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ, Ep) ∞ P)
        (RS : TensorRawCutoffPreparation A BS₀ TS Ds)
        (RP : TensorLocalRawPreparation B univ BP₀ TP Dp),
      rho ≤ min B.buffer A.buffer →
      ∀ (Omega : Fin A.count → Set Es) (Q : Fin pcount → Set Ep),
      (∀ i, IsCompact (Omega i)) → (∀ i, IsCompact (Q i)) →
      (∀ i, Omega i ⊆ (A.chart i).target) → (∀ i, Q i ⊆ (B.chart i).target) →
      (∀ i, bufferedSamplingCoordinates A i ⊆ Omega i) →
      (∀ i, tensorLocalSamplingCoordinates B i ⊆ Q i) →
      ∀ tau ell t : ℝ, 0 < tau → tau ≤ ell → ell ≤ t → t ≤ 1 →
      ∀ (u : P × M → Ey),
      (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B.chart u i)
        (incrementsOriginalDifferentiation A B.chart i)) →
      ∀ (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, Es) x)),
      (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart H i)
        (incrementsOriginalDifferentiation A B.chart i)) →
      ∀ budget : ℝ,
      (parameterLocalOriginalTotalPairWeighted A B u H r t
        (incrementsOriginalEvaluation A B.chart Omega Q univ)).toReal ≤ budget →
      let S := incrementsOriginalEvaluation A B.chart Omega Q univ
      let mu := (volume : Measure (Ep × Es))
      let K := fixedSmoothingKernel mu rho hrho r
      let chi := parameterLocalProductCutoff A B
        (squareNormalizedCutoff RS.raw) (tensorLocalNormalizedCutoff RP.raw)
      let SF := parameterLocalMapSmoothing (parameterLocalProductFamily A B) mu K ell chi u
      let SH := tensorLocalParameterSmoothing A B hA mu K ell chi H
      ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ SF ∧
      (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart SH i)
        (incrementsOriginalDifferentiation A B.chart i)) ∧
      parameterLocalOriginalTotalPairWeighted A B
        (fun z => u z - SF z) (fun p x => H p x - SH p x)
        m tau S ≠ ⊤ ∧
      (parameterLocalOriginalTotalPairWeighted A B
        (fun z => u z - SF z) (fun p x => H p x - SH p x)
        m tau S).toReal ≤
        C * (budget * (ell/t)^r +
          (parameterLocalOriginalTotalPairWeighted A B u H m t
            (incrementsOriginalEvaluation A B.chart Omega Q univ)).toReal * (tau/t)^r) ∧
      parameterLocalOriginalTotalPairWeighted A B SF SH
        m tau S ≠ ⊤ ∧
      (parameterLocalOriginalTotalPairWeighted A B SF SH
        m tau S).toReal ≤ C * budget := by
  obtain ⟨hC,hpair⟩ := round4_actual_local_set_pair_smoothing
    (n := n) (d := d) (N := N) (M := M) (P := P)
    BS₀ TS BP₀ TP hBS₀ hTS hBP₀ hTP Ds Dp rho hrho m r
  refine ⟨hC,?_⟩
  intro pcount A B hA hB RS RP hbuffer Omega Q hOmega hQ hOT hQT hsource hparameter
    tau ell t htau htaul helt ht1 u hu H hH budget hbudget
  exact hpair pcount A B hA hB univ RS RP hbuffer Omega Q hOmega hQ hOT hQT hsource hparameter
    (incrementsOriginalEvaluation A B.chart Omega Q univ)
    (fun _ _ hy => ⟨hy.1,Set.mem_univ _⟩)
    tau ell t htau htaul helt ht1 u hu H hH budget hbudget


#print axioms round4_actual_local_set_pair_smoothing
#print axioms round4_actual_closed_parameter_same_domain_pair
#print axioms round4PreparedPairConstant_congr_prefix
end
end GlobalEmbedding.Continuation
