import Smoothing.Round3OuterLowLocalPairTail
import Smoothing.Round3OuterTargetC0Algebra
import Probes.ActualRepairTargetGerm
import Smoothing.Round3OuterClosedPair
import Smoothing.Round3OuterLocalSetPair
import Smoothing.Round3OuterPreparedPair
import Smoothing.Round3OuterPreparedPairGain
import Smoothing.ParameterRound2CompactPair

/-!
# The actual full-parameter pair on genuine compact original norm domains

The input and output norms are the unchanged original total-joint C2-map plus
C0-tensor norms. Compact coordinate domains prove every required fixed-order
finiteness guard. The only numerical input is the original low weighted pair
budget, and the high tail retains its actual original weighted norm. One
normalized product cutoff, signed kernel and scale produce the same native
map and native tensor in the tail and gain conclusions. Uniform constants
precede every atlas, compact norm domain, raw preparation, field and scale.
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

local instance round3Outer_actualLocalTargetControlChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance round3Outer_actualLocalTargetControlIsManifold : IsManifold
    𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) P M

local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ey" => EuclideanSpace ℝ (Fin N)

/-- A local-parameter actual repair target. The literal SH-a gamma(F0)
has its original C0 defect controlled by the smoothing tail, inherited defect,
and explicit reserve. Full joint C2 control of the SAME SF is simultaneous. -/
theorem round3Outer_exists_uniform_actual_local_target_low_control
    (BS₀ TS BP₀ TP : ℕ → ℝ)
    (hBS₀ : ∀ j, 0 ≤ BS₀ j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP₀ : ∀ j, 0 ≤ BP₀ j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (rho : ℝ) (hrho : 0 < rho) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
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
      (∀ i, IsCompact (S i)) →
      (∀ i, S i ⊆ round3OuterOriginalEvaluation A B parameterSet i) →
      ∀ ell t : ℝ, 0 < ell → ell ≤ t → t ≤ 1 →
      ∀ (u : P × M → Ey),
      (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B.chart u i)
        (incrementsOriginalDifferentiation A B.chart i)) →
      ∀ (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, Es) x)),
      (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart H i)
        (incrementsOriginalDifferentiation A B.chart i)) →
      (∀ p x, (H p x).IsSymm) →
      ∀ (F0 : P × M → Ey), ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ F0 →
      ∀ (a inherited reference : ℝ), 0 ≤ a →
      let h0 := fun p x => inducedMetric (I := 𝓘(ℝ,Es)) (fun y => F0 (p,y)) x
      (paperAtlasCj 0 (incrementsOriginalTensorCoordinates A B.chart (fun p x => H p x-h0 p x))
        (incrementsOriginalDifferentiation A B.chart)
        S).toReal ≤ inherited →
      (paperAtlasCj 0 (incrementsOriginalTensorCoordinates A B.chart h0)
        (incrementsOriginalDifferentiation A B.chart)
        S).toReal ≤ reference →
      ∀ budget : ℝ,
      (parameterLocalOriginalTotalPairWeighted A B u H r t
        (incrementsOriginalEvaluation A B.chart Omega Q univ)).toReal ≤ budget →
      let mu := (volume : Measure (Ep × Es))
      let K := fixedSmoothingKernel mu rho hrho r
      let chi := parameterLocalProductCutoff A B
        (squareNormalizedCutoff RS.raw) (tensorLocalNormalizedCutoff RP.raw)
      let SF := parameterLocalMapSmoothing (parameterLocalProductFamily A B) mu K ell chi u
      let SH := tensorLocalParameterSmoothing A B hA mu K ell chi H
      let Target := fun p x => SH p x-a • h0 p x
      ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ SF ∧
      (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart Target i)
        (incrementsOriginalDifferentiation A B.chart i)) ∧
      (∀ p x, (Target p x).IsSymm) ∧
      paperAtlasCj 2 (incrementsOriginalMapCoordinates A B.chart (fun z => u z-SF z))
        (incrementsOriginalDifferentiation A B.chart) S ≠ ⊤ ∧
      (paperAtlasCj 2 (incrementsOriginalMapCoordinates A B.chart (fun z => u z-SF z))
        (incrementsOriginalDifferentiation A B.chart) S).toReal ≤ C*budget*(ell/t)^r ∧
      paperAtlasCj 0 (incrementsOriginalTensorCoordinates A B.chart (fun p x => Target p x-h0 p x))
        (incrementsOriginalDifferentiation A B.chart) S ≠ ⊤ ∧
      (paperAtlasCj 0 (incrementsOriginalTensorCoordinates A B.chart (fun p x => Target p x-h0 p x))
        (incrementsOriginalDifferentiation A B.chart) S).toReal ≤
          C*budget*(ell/t)^r+inherited+a*reference := by
  obtain ⟨C,hC,hlow⟩ := round3Outer_exists_uniform_local_low_pair_tail
    (n := n) (d := d) (N := N) (M := M) (P := P)
    BS₀ TS BP₀ TP hBS₀ hTS hBP₀ hTP Ds Dp rho hrho r
  refine ⟨C,hC,?_⟩
  intro pcount A B hA hB parameterSet RS RP hbuffer Omega Q hOmega hQ hOT hQT hsource hparameter
    S hScompact hS ell t hell helt ht1 u hu H hH hHs F0 hF0 a inherited reference ha h0 hInherited hReference
    budget hbudget mu K chi SF SH Target
  have hp := hlow pcount A B hA hB parameterSet RS RP hbuffer Omega Q hOmega hQ hOT hQT
    hsource hparameter S hS ell t hell helt ht1 u hu H hH budget hbudget
  dsimp only at hp
  have hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B.chart i := fun i _ hy => (hS i hy).1
  have hRef := parameterRound2_inducedMetric_originalCoordinates_contDiffOn A B.chart hA hB F0 hF0
  have hRefs : ∀ p x, (h0 p x).IsSymm := fun p x =>
    (inducedMetric_isPosSemidef (I := 𝓘(ℝ,Es)) (fun y => F0 (p,y)) x).isSymm
  have hSHs : ∀ p x, (SH p x).IsSymm := fun p x =>
    tensorFamilySmoothing_isSymm (parameterLocalProductFamily A B) mu K ell chi
      (tensorLocalParameterFrame A B hA) (fun z => H z.1 z.2) (fun z => hHs z.1 z.2) (p,x)
  have hsum : paperAtlasCj 2 (incrementsOriginalMapCoordinates A B.chart (fun z => u z-SF z))
      (incrementsOriginalDifferentiation A B.chart) S +
      paperAtlasCj 0 (incrementsOriginalTensorCoordinates A B.chart (fun p x => H p x-SH p x))
      (incrementsOriginalDifferentiation A B.chart) S ≠ ⊤ := by
    simpa only [parameterLocalOriginalTotalPairWeighted,paperAtlasWeighted,
      Finset.sum_range_one,pow_zero,zero_add,one_mul] using hp.2.2.1
  have hsumBound : (paperAtlasCj 2 (incrementsOriginalMapCoordinates A B.chart (fun z => u z-SF z))
      (incrementsOriginalDifferentiation A B.chart) S +
      paperAtlasCj 0 (incrementsOriginalTensorCoordinates A B.chart (fun p x => H p x-SH p x))
      (incrementsOriginalDifferentiation A B.chart) S).toReal ≤ C*budget*(ell/t)^r := by
    simpa only [parameterLocalOriginalTotalPairWeighted,paperAtlasWeighted,
      Finset.sum_range_one,pow_zero,zero_add,one_mul] using hp.2.2.2
  have hmap := (ENNReal.toReal_mono hsum (le_add_right (le_refl _))).trans hsumBound
  have htensor := (ENNReal.toReal_mono hsum (le_add_left (le_refl _))).trans hsumBound
  have htarget := round3_original_target_C0_from_smoothing_error A B.chart S hScompact hSO H SH h0
    hH hp.2.1 hRef hHs hSHs hRefs ell a (C*budget*(ell/t)^r) inherited reference ha
    htensor hInherited hReference
  refine ⟨hp.1,fun i => (hp.2.1 i).sub ((hRef i).const_smul a),
    fun p x => (hSHs p x).sub ((hRefs p x).smul a),
    (ENNReal.add_ne_top.mp hsum).1,hmap,htarget⟩

#print axioms round3Outer_exists_uniform_actual_local_target_low_control
end
end GlobalEmbedding.Continuation
