import Probes.ActualOriginalCoreJets
import Probes.ActualJointChartTransfer
import Smoothing.ParameterRound2MetricRegularity

/-! The ORIGINAL C2 map norm controls the true native two-jet in any fixed
actual adapted chart. Every coordinate factor is explicit. No dependence on
the perturbed map, smoothing scale, number of charts or higher input order
enters the constant. This is the original-norm entrance to reference geometry
stability, with the true parameter coordinates and source derivatives.
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

def round3OriginalNativeMapCoordinates (A : BufferedAtlas M Es)
    (B : Fin c → OpenPartialHomeomorph P Ep) (F : P × M → Ey)
    (i : Fin A.count × Fin c) (z : X) : Ey :=
  F ((B i.2).symm z.1,(A.chart i.1).symm z.2)

theorem round3_original_native_map_coordinates_eq (A : BufferedAtlas M Es)
    (B : Fin c → OpenPartialHomeomorph P Ep) (F : P × M → Ey)
    (i : Fin A.count × Fin c) :
    round3OriginalNativeMapCoordinates A B F i = (EuclideanSpace.equiv (Fin N) ℝ).symm ∘
      incrementsOriginalMapCoordinates A B F i ∘ parameterTensorModelEquiv n d := by
  funext z
  have hp := congrArg Prod.fst ((parameterTensorModelEquiv n d).symm_apply_apply z)
  have hx := congrArg Prod.snd ((parameterTensorModelEquiv n d).symm_apply_apply z)
  change incrementsOriginalParameterPoint (parameterTensorModelEquiv n d z) = z.1 at hp
  change incrementsOriginalSourcePoint (parameterTensorModelEquiv n d z) = z.2 at hx
  simp only [Function.comp_apply,incrementsOriginalMapCoordinates,
    incrementsOriginalJointPoint,ContinuousLinearEquiv.symm_apply_apply,hp,hx]
  rfl

theorem round3_original_C2_native_jets (A : BufferedAtlas M Es)
    (B : Fin c → OpenPartialHomeomorph P Ep) (F : P × M → Ey)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (hF : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B F i)
      (incrementsOriginalDifferentiation A B i))
    (hFinite : paperAtlasCj 2 (incrementsOriginalMapCoordinates A B F)
      (incrementsOriginalDifferentiation A B) S ≠ ⊤)
    (R : ℝ) (hR : (paperAtlasCj 2 (incrementsOriginalMapCoordinates A B F)
      (incrementsOriginalDifferentiation A B) S).toReal ≤ R)
    (i : Fin A.count × Fin c) (j : ℕ) (hj : j ≤ 2) (z : X)
    (hz : parameterTensorModelEquiv n d z ∈ S i) :
    ‖iteratedFDeriv ℝ j (round3OriginalNativeMapCoordinates A B F i) z‖ ≤
      actualOriginalMapJetCost n d N 0*R := by
  have hf : paperAtlasWeighted 2 0 1 (incrementsOriginalMapCoordinates A B F)
      (incrementsOriginalDifferentiation A B) S ≠ ⊤ := by
    simpa only [paperAtlasWeighted,Finset.sum_range_one,pow_zero,zero_add,one_mul] using hFinite
  have h := paperAtlasWeighted_native_shifted_joint_jet_le
    (parameterTensorModelEquiv n d) (EuclideanSpace.equiv (Fin N) ℝ).symm
    2 0 1 (by norm_num) (incrementsOriginalMapCoordinates A B F)
    (incrementsOriginalDifferentiation A B) S
    (parameterRound2_originalDifferentiation_open A B) hSO hF hf i (k := 0) (b := j)
    le_rfl hj hz
  rw [← round3_original_native_map_coordinates_eq] at h
  simp only [zero_add,pow_zero,one_mul,paperAtlasWeighted,Finset.sum_range_one] at h
  convert h.trans (mul_le_mul_of_nonneg_left hR (actualOriginalMapJetCost_nonneg n d N 0)) using 1
  · interval_cases j <;> rfl
  · rfl

def round3OriginalAdaptedTransition (A : BufferedAtlas M Es) (a : Fin A.count)
    (e : Ep → OpenPartialHomeomorph M Es) (z : X) : X :=
  (z.1,A.chart a ((e z.1).symm z.2))

def round3OriginalC2AdaptedCost (n d N : ℕ) (T : ℕ → ℝ) : ℝ :=
  (∑ j ∈ Finset.range 3, actualFastChartTransferCost T j)*actualOriginalMapJetCost n d N 0

theorem round3OriginalC2AdaptedCost_nonneg (n d N : ℕ) (T : ℕ → ℝ)
    (hT : ∀ j, 0 ≤ T j) : 0 ≤ round3OriginalC2AdaptedCost n d N T :=
  mul_nonneg (Finset.sum_nonneg fun j _ => actualFastChartTransferCost_nonneg T hT j)
    (actualOriginalMapJetCost_nonneg n d N 0)

/-- Actual chart transition and original C2 norm, retaining all parameter
responses. The adapted-map jets are conclusions; only fixed chart jets are
primitive geometry inputs. -/
theorem round3_original_C2_actual_adapted_jets (T : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j)
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep) (F : P × M → Ey)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (hF : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B F i)
      (incrementsOriginalDifferentiation A B i))
    (hFinite : paperAtlasCj 2 (incrementsOriginalMapCoordinates A B F)
      (incrementsOriginalDifferentiation A B) S ≠ ⊤)
    (R : ℝ) (hR0 : 0 ≤ R) (hR : (paperAtlasCj 2 (incrementsOriginalMapCoordinates A B F)
      (incrementsOriginalDifferentiation A B) S).toReal ≤ R)
    (i : Fin A.count × Fin c) (e : Ep → OpenPartialHomeomorph M Es)
    (O : Set X) (hO : IsOpen O)
    (hTransition : ContDiffOn ℝ ∞ (round3OriginalAdaptedTransition A i.1 e) O)
    (hSource : ∀ z ∈ O, (e z.1).symm z.2 ∈ (A.chart i.1).source)
    (hParameter : ∀ z ∈ O, z.1 ∈ (B i.2).target)
    (z : X) (hz : z ∈ O)
    (hSample : parameterTensorModelEquiv n d (round3OriginalAdaptedTransition A i.1 e z) ∈ S i)
    (hChartJets : ∀ j, 1 ≤ j → j ≤ 2 →
      ‖iteratedFDeriv ℝ j (round3OriginalAdaptedTransition A i.1 e) z‖ ≤ T j) :
    ∀ j ≤ 2, ‖iteratedFDeriv ℝ j
      (fun w : X => F ((B i.2).symm w.1,(e w.1).symm w.2)) z‖ ≤
      round3OriginalC2AdaptedCost n d N T*R := by
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
  intro j hj
  have hTransfer := actual_fast_joint_chart_transfer T hT j phi f O V hO hV hTransition hf hMap
    z hz 1 1 (actualOriginalMapJetCost n d N 0*R) (by norm_num) le_rfl
    (fun k hk => by simpa only [one_pow,one_mul] using
      round3_original_C2_native_jets A B F S hSO hF hFinite R hR i k (hk.trans hj) (phi z) hSample)
    (fun k hk hkj => by simpa only [one_pow,one_mul] using hChartJets k hk (hkj.trans hj))
  rw [(hEq.iteratedFDeriv ℝ j).eq_of_nhds] at hTransfer
  simp only [one_pow,one_mul] at hTransfer
  have hCost : actualFastChartTransferCost T j ≤ ∑ k ∈ Finset.range 3, actualFastChartTransferCost T k :=
    Finset.single_le_sum (fun k _ => actualFastChartTransferCost_nonneg T hT k) (by simp; omega)
  exact hTransfer.trans ((mul_le_mul_of_nonneg_right hCost
    (mul_nonneg (actualOriginalMapJetCost_nonneg n d N 0) hR0)).trans_eq (by
      unfold round3OriginalC2AdaptedCost
      ring))

#print axioms round3_original_C2_native_jets
#print axioms round3_original_C2_actual_adapted_jets
end GlobalEmbedding.Continuation
