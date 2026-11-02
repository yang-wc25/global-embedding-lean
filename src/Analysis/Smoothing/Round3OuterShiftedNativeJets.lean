import Smoothing.Round3OuterC2SpatialDifference
import Smoothing.Round3OuterShiftedChartTransfer

/-! The genuine original weighted C2-base map norm controls the actual
adapted map's shifted joint jets through one fixed reference transition.
All constants precede the new map and scale. No atlas-count factor or
extra negative power of ell is inserted.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff Topology ENNReal BigOperators
namespace GlobalEmbedding.Continuation
variable {n d N c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × Es

theorem round3_original_weighted_native_jets
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep) (F : P × M → Ey)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (hF : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B F i)
      (incrementsOriginalDifferentiation A B i))
    (j : ℕ) (ell : ℝ) (hell : 0 < ell)
    (hFinite : paperAtlasWeighted 2 j ell (incrementsOriginalMapCoordinates A B F)
      (incrementsOriginalDifferentiation A B) S ≠ ⊤)
    (R : ℝ) (hR : (paperAtlasWeighted 2 j ell (incrementsOriginalMapCoordinates A B F)
      (incrementsOriginalDifferentiation A B) S).toReal ≤ R)
    (i : Fin A.count × Fin c) (k b : ℕ) (hk : k ≤ j) (hb : b ≤ 2) (z : X)
    (hz : parameterTensorModelEquiv n d z ∈ S i) :
    ell^k*‖iteratedFDeriv ℝ (k+b) (round3OriginalNativeMapCoordinates A B F i) z‖ ≤
      actualOriginalMapJetCost n d N j*R := by
  rw [round3_original_native_map_coordinates_eq]
  have h := paperAtlasWeighted_native_shifted_joint_jet_le
    (parameterTensorModelEquiv n d) (EuclideanSpace.equiv (Fin N) ℝ).symm
    2 j ell hell (incrementsOriginalMapCoordinates A B F)
    (incrementsOriginalDifferentiation A B) S
    (parameterRound2_originalDifferentiation_open A B) hSO hF hFinite i hk hb hz
  exact h.trans (mul_le_mul_of_nonneg_left hR (actualOriginalMapJetCost_nonneg n d N j))

def round3OriginalShiftedAdaptedCost (n d N : ℕ) (T : ℕ → ℝ) (j : ℕ) : ℝ :=
  (∑ l ∈ Finset.range (j+3), actualFastChartTransferCost T l)*actualOriginalMapJetCost n d N j

theorem round3OriginalShiftedAdaptedCost_nonneg (n d N : ℕ) (T : ℕ → ℝ)
    (hT : ∀ j, 0 ≤ T j) (j : ℕ) : 0 ≤ round3OriginalShiftedAdaptedCost n d N T j :=
  mul_nonneg (Finset.sum_nonneg fun l _ => actualFastChartTransferCost_nonneg T hT l)
    (actualOriginalMapJetCost_nonneg n d N j)

/-- Fixed-reference coordinate transfer of the original shifted norm.
The same actual map and all its parameter derivatives are retained. -/
theorem round3_original_weighted_actual_adapted_jets
    (T : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j)
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep) (F : P × M → Ey)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (hF : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B F i)
      (incrementsOriginalDifferentiation A B i))
    (j : ℕ) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hFinite : paperAtlasWeighted 2 j ell (incrementsOriginalMapCoordinates A B F)
      (incrementsOriginalDifferentiation A B) S ≠ ⊤)
    (R : ℝ) (hR0 : 0 ≤ R) (hR : (paperAtlasWeighted 2 j ell (incrementsOriginalMapCoordinates A B F)
      (incrementsOriginalDifferentiation A B) S).toReal ≤ R)
    (i : Fin A.count × Fin c) (e : Ep → OpenPartialHomeomorph M Es)
    (O : Set X) (hO : IsOpen O)
    (hTransition : ContDiffOn ℝ ∞ (round3OriginalAdaptedTransition A i.1 e) O)
    (hSource : ∀ z ∈ O, (e z.1).symm z.2 ∈ (A.chart i.1).source)
    (hParameter : ∀ z ∈ O, z.1 ∈ (B i.2).target)
    (z : X) (hz : z ∈ O)
    (hSample : parameterTensorModelEquiv n d (round3OriginalAdaptedTransition A i.1 e z) ∈ S i)
    (hChartJets : ∀ l, 1 ≤ l → l ≤ j+2 →
      ‖iteratedFDeriv ℝ l (round3OriginalAdaptedTransition A i.1 e) z‖ ≤ T l) :
    ∀ k ≤ j, ∀ b ≤ 2, ell^k*‖iteratedFDeriv ℝ (k+b)
      (fun w : X => F ((B i.2).symm w.1,(e w.1).symm w.2)) z‖ ≤
      round3OriginalShiftedAdaptedCost n d N T j*R := by
  let phi := round3OriginalAdaptedTransition A i.1 e
  let f := round3OriginalNativeMapCoordinates A B F i
  let V := (parameterTensorModelEquiv n d) ⁻¹' incrementsOriginalDifferentiation A B i
  have hV : IsOpen V := (parameterRound2_originalDifferentiation_open A B i).preimage
    (parameterTensorModelEquiv n d).continuous
  have hf : ContDiffOn ℝ ∞ f V := by
    rw [show f = (EuclideanSpace.equiv (Fin N) ℝ).symm ∘
      incrementsOriginalMapCoordinates A B F i ∘ parameterTensorModelEquiv n d from
      round3_original_native_map_coordinates_eq A B F i]
    exact (EuclideanSpace.equiv (Fin N) ℝ).symm.contDiff.comp_contDiffOn
      ((hF i).comp (parameterTensorModelEquiv n d).contDiff.contDiffOn (fun _ hx => hx))
  have hMap : MapsTo phi O V := by
    intro w hw
    have he := (parameterTensorModelEquiv n d).symm_apply_apply (phi w)
    have hp := congrArg Prod.fst he
    have hx := congrArg Prod.snd he
    change incrementsOriginalParameterPoint (parameterTensorModelEquiv n d (phi w)) = w.1 at hp
    change incrementsOriginalSourcePoint (parameterTensorModelEquiv n d (phi w)) =
      A.chart i.1 ((e w.1).symm w.2) at hx
    change _ ∧ _
    rw [hp,hx]
    exact ⟨(A.chart i.1).map_source (hSource w hw),hParameter w hw⟩
  have hEq : f ∘ phi =ᶠ[𝓝 z] (fun w : X => F ((B i.2).symm w.1,(e w.1).symm w.2)) := by
    filter_upwards [hO.mem_nhds hz] with w hw
    exact congrArg (fun x => F ((B i.2).symm w.1,x)) ((A.chart i.1).left_inv (hSource w hw))
  intro k hk b hb
  have hTransfer := round3_fixed_chart_base_two_transfer T hT k b hb phi f O V hO hV
    hTransition hf hMap z hz ell (actualOriginalMapJetCost n d N j*R) hell hell1
    (fun a ha c hc => round3_original_weighted_native_jets A B F S hSO hF j ell hell
      hFinite R hR i a c (ha.trans hk) hc (phi z) hSample)
    (fun a ha hab => hChartJets a ha (by omega))
  rw [(hEq.iteratedFDeriv ℝ (k+b)).eq_of_nhds] at hTransfer
  have hCost : actualFastChartTransferCost T (k+b) ≤
      ∑ l ∈ Finset.range (j+3), actualFastChartTransferCost T l :=
    Finset.single_le_sum (fun l _ => actualFastChartTransferCost_nonneg T hT l) (by simp; omega)
  exact hTransfer.trans ((mul_le_mul_of_nonneg_right hCost
    (mul_nonneg (actualOriginalMapJetCost_nonneg n d N j) hR0)).trans_eq (by
      unfold round3OriginalShiftedAdaptedCost
      ring))

#print axioms round3_original_weighted_native_jets
#print axioms round3_original_weighted_actual_adapted_jets
end GlobalEmbedding.Continuation
