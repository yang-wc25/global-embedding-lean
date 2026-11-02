import Probes.ActualRepairGermNormIdentity
import Smoothing.ParameterRound2CrossGermMapNorms

/-! The actual metric update consumes the finite-increment conclusion on the
same samples. The map tail is differentiated exactly once in Cross; no square
of the smoothing defect is inserted. This lemma is consumed internally by
the raw-construction wrapper. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
variable {n d N c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

def actualRepairCrossCost (n d N j : ℕ) : ℝ :=
  (j+1)*linearModelFactor (parameterTensorModelEquiv n d).symm j*2^(j+1)*
    parameterRound2_mapWeightedJetCost n d N 2 j*parameterRound2_mapWeightedJetCost n d N 1 j

theorem actualRepairCrossCost_nonneg (n d N j : ℕ) : 0 ≤ actualRepairCrossCost n d N j := by
  have hL := linearModelFactor_nonneg (parameterTensorModelEquiv n d).symm j
  have h2 := parameterRound2_mapWeightedJetCost_nonneg n d N 2 j
  have h1 := parameterRound2_mapWeightedJetCost_nonneg n d N 1 j
  unfold actualRepairCrossCost
  positivity

theorem actual_repair_germ_finite_increment_consumer
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep) (hA : IsSmoothBufferedAtlas A)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (G SG U : P × M → V)
    (hG : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B G i)
      (incrementsOriginalDifferentiation A B i))
    (hSG : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B SG i)
      (incrementsOriginalDifferentiation A B i))
    (hU : ∀ i, ∃ V0 : Set (Fin (n+d) → ℝ), IsOpen V0 ∧ S i ⊆ V0 ∧
      V0 ⊆ incrementsOriginalDifferentiation A B i ∧
      ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B U i) V0)
    (hstar h0 SH : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (delta deltaNext tau : ℝ) (hdelta : delta ≠ 0) (hdelta0 : 0 ≤ delta)
    (hdeltaNext : deltaNext ≠ 0) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (j : ℕ) (CE CU rate : ℝ) (hCU : 0 ≤ CU) :
    let H := fun p x => (delta^2)⁻¹ • (hstar p x-inducedMetric (I := 𝓙) (fun y => G (p,y)) x)
    let E := incrementsOriginalMetricError SG U (fun p x => SH p x-(deltaNext/delta)^2 • h0 p x) delta
    let Hnext := fun p x => (deltaNext^2)⁻¹ • (hstar p x-inducedMetric (I := 𝓙) (fun y => G (p,y)+U (p,y)) x)
    let O := incrementsOriginalDifferentiation A B
    let WT := fun T => paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates A B T) O S
    let WM := fun b F => paperAtlasWeighted b j tau (incrementsOriginalMapCoordinates A B F) O S
    (∀ i, ∃ V0 : Set (Fin (n+d) → ℝ), IsOpen V0 ∧ S i ⊆ V0 ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B (fun p x => H p x-SH p x) i) V0) →
    (∀ i, ∃ V0 : Set (Fin (n+d) → ℝ), IsOpen V0 ∧ S i ⊆ V0 ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B E i) V0) →
    WT (fun p x => H p x-SH p x) ≠ ⊤ → WM 2 (fun z => G z-SG z) ≠ ⊤ →
    WT E ≠ ⊤ → (WT E).toReal ≤ CE*rate →
    WM 1 U ≠ ⊤ → (WM 1 U).toReal ≤ CU*delta →
    (∀ i, ∃ V0 : Set (Fin (n+d) → ℝ), IsOpen V0 ∧ S i ⊆ V0 ∧ V0 ⊆ O i ∧
      ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B (fun z => G z+U z) i) V0 ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B (fun p x => Hnext p x-h0 p x) i) V0) ∧
    WT (fun p x => Hnext p x-h0 p x) ≠ ⊤ ∧
    (WT (fun p x => Hnext p x-h0 p x)).toReal ≤ (deltaNext^2)⁻¹ *
      (CE*rate + delta^2*(WT (fun p x => H p x-SH p x)).toReal +
        actualRepairCrossCost n d N j*(WM 2 (fun z => G z-SG z)).toReal*(CU*delta)) := by
  intro H E Hnext O WT WM hTail hE hTf hMf hEf hEb hUf hUb
  choose UI hUI hSUI hUIO hUreg using hU
  have hFreg : ∀ i, ContDiffOn ℝ ∞
      (incrementsOriginalMapCoordinates A B (fun z => G z-SG z) i) (UI i) :=
    fun i => ((hG i).sub (hSG i)).mono (hUIO i)
  have hcross := parameterRound2_original_metricCrossTerm_from_map_germ_norms A B hA S hSO
    UI hUI hUIO hSUI (fun z => G z-SG z) U hFreg hUreg j tau htau htau1 hMf hUf
  have hmaps : ∀ i, ∃ V0 : Set (Fin (n+d) → ℝ), IsOpen V0 ∧ S i ⊆ V0 ∧ V0 ⊆ O i ∧
      ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B G i) V0 ∧
      ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B SG i) V0 ∧
      ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B U i) V0 := by
    intro i
    exact ⟨UI i,hUI i,hSUI i,hUIO i,(hG i).mono (hUIO i),(hSG i).mono (hUIO i),hUreg i⟩
  have hid := actual_repair_weighted_norm_identity_germs A B hA S hSO G SG U hmaps
    hstar h0 SH delta deltaNext hdelta hdeltaNext j tau htau hTail hE
    (fun i => ⟨UI i,hUI i,hSUI i,hcross.1 i⟩) hTf hEf hcross.2.1
  refine ⟨?_,hid.2.1,hid.2.2.trans ?_⟩
  · intro i
    obtain ⟨VN,hVN,hSVN,hVNO,hNreg⟩ := hid.1 i
    refine ⟨VN ∩ UI i,hVN.inter (hUI i),fun z hz => ⟨hSVN hz,hSUI i hz⟩,
      fun z hz => hVNO hz.1,?_,hNreg.mono inter_subset_left⟩
    exact ((hG i).mono (fun z hz => hVNO hz.1)).add ((hUreg i).mono inter_subset_right)
  · apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (sq_nonneg _))
    have hcb : (paperAtlasWeighted 0 j tau
        (incrementsOriginalTensorCoordinates A B (fun p x => metricCrossTerm (I := 𝓙)
          (fun y => G (p,y)-SG (p,y)) (fun y => U (p,y)) x)) O S).toReal ≤
        actualRepairCrossCost n d N j*(WM 2 (fun z => G z-SG z)).toReal*(CU*delta) :=
      hcross.2.2.trans (mul_le_mul_of_nonneg_left hUb
        (mul_nonneg (actualRepairCrossCost_nonneg n d N j) ENNReal.toReal_nonneg))
    linarith

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_repair_germ_finite_increment_consumer
