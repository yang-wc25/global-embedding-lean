import Smoothing.ParameterFiniteGeometry
import Smoothing.Round4SpatialWeightedNativeJets
import Smoothing.Round4SpatialTriangularTransfer
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

def round4OriginalSpatialAdaptedCost (n d N : ℕ) (T : ℕ → ℝ) (j : ℕ) : ℝ :=
  parameterJetTransferConstant
    (parameterSpatialTransferCoefficient (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin N))
      (fun _ => 1) T) T 1 j *
    parameterModelNativeFactor (EuclideanSpace.equiv (Fin d) ℝ)
      (EuclideanSpace.equiv (Fin n) ℝ) (EuclideanSpace.equiv (Fin N) ℝ) j

theorem round4OriginalSpatialAdaptedCost_nonneg (n d N : ℕ) (T : ℕ → ℝ)
    (hT : ∀ j, 0 ≤ T j) (j : ℕ) : 0 ≤ round4OriginalSpatialAdaptedCost n d N T j :=
  mul_nonneg (parameterJetTransferConstant_nonneg
    (parameterSpatialTransferCoefficient_nonneg (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin N))
      (fun _ => zero_le_one) hT) hT 1 j)
    (parameterModelNativeFactor_nonneg _ _ _ j)

theorem round4OriginalSpatialAdaptedCost_congr_prefix (n d N j : ℕ)
    {T₁ T₂ : ℕ → ℝ} (hT : ∀ a ≤ j+2, T₁ a = T₂ a) :
    round4OriginalSpatialAdaptedCost n d N T₁ j = round4OriginalSpatialAdaptedCost n d N T₂ j := by
  unfold round4OriginalSpatialAdaptedCost
  rw [parameterJetTransferConstant_congr_prefix 1 j
    (fun a ha => parameterSpatialTransferCoefficient_congr_prefix a
      (fun _ _ => rfl) (fun b _ hb => hT b (by omega)))
    (fun a ha => hT a (by omega))]

theorem round4_original_spatial_weighted_actual_adapted_jets
    (T : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j)
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep) (F : P × M → Ey)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (hF : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B F i)
      (incrementsOriginalDifferentiation A B i))
    (j : ℕ) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hFinite : parameterSpatialWeighted (n := n) (d := d) j ell (incrementsOriginalMapCoordinates A B F)
      (incrementsOriginalDifferentiation A B) S ≠ ⊤)
    (R : ℝ) (hR0 : 0 ≤ R) (hR : (parameterSpatialWeighted (n := n) (d := d) j ell (incrementsOriginalMapCoordinates A B F)
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
    ∀ k ≤ j, ell^k*‖iteratedFDeriv ℝ k
      (spatialNativeJet (fun w : X => F ((B i.2).symm w.1,(e w.1).symm w.2))) z‖ ≤
      round4OriginalSpatialAdaptedCost n d N T j*R := by
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
  intro k hk
  let C := parameterSpatialTransferCoefficient Es Ey (fun _ => 1) T
  have hC : ∀ a, 0 ≤ C a := parameterSpatialTransferCoefficient_nonneg Es Ey (fun _ => zero_le_one) hT
  let Cnative := parameterModelNativeFactor (EuclideanSpace.equiv (Fin d) ℝ)
    (EuclideanSpace.equiv (Fin n) ℝ) (EuclideanSpace.equiv (Fin N) ℝ) j
  have hN : 0 ≤ Cnative := parameterModelNativeFactor_nonneg _ _ _ j
  have hTransfer := round4_spatial_triangular_slow_jet (fun p : Ep => p)
    (fun w => (phi w).2) f O V hO hV hTransition hf hMap T hT hz k ell (Cnative*R) hell hell1
    (fun a ha => round4_original_spatial_weighted_native_jets A B F S hSO hF j ell hell
      hFinite R hR i a (ha.trans hk) (phi z) hSample)
    (fun a ha haj => hChartJets a ha (by omega))
  change ell^k*‖iteratedFDeriv ℝ k (spatialNativeJet (f ∘ phi)) z‖ ≤
    parameterJetTransferCore C T k * (Cnative*R) at hTransfer
  rw [((spatialNativeJet_eventuallyEq hEq).iteratedFDeriv ℝ k).eq_of_nhds] at hTransfer
  have hCost : parameterJetTransferCore C T k ≤ parameterJetTransferConstant C T 1 j := by
    unfold parameterJetTransferConstant
    simp only [Nat.cast_one, one_mul]
    exact Finset.single_le_sum (fun a _ => parameterJetTransferCore_nonneg hC hT a) (by simpa using hk)
  exact hTransfer.trans ((mul_le_mul_of_nonneg_right hCost (mul_nonneg hN hR0)).trans_eq (by
    unfold round4OriginalSpatialAdaptedCost
    dsimp only [C, Cnative]
    ring))

#print axioms round4_original_spatial_weighted_actual_adapted_jets
#print axioms round4OriginalSpatialAdaptedCost_congr_prefix
end GlobalEmbedding.Continuation
