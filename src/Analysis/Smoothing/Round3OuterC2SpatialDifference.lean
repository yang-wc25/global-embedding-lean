import Smoothing.Round3OuterC2NativeJets
import Probes.ActualSourceRestriction

/-! True source first and second derivatives of two actual maps are compared
by their original C2 difference, through the same fixed adapted chart. This
retains native Hessians and all parameter dependence; no candidate frame or
separately supplied two-jet discrepancy is introduced.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff Topology ENNReal BigOperators
namespace GlobalEmbedding.Continuation

private theorem two_jet_difference_from_iterated {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f g : E → Y) (x : E) (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (C : ℝ) (hC : 0 ≤ C)
    (hjets : ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (fun y => f y-g y) x‖ ≤ C) :
    ‖fderiv ℝ f x-fderiv ℝ g x‖ ≤ C ∧
    ‖fderiv ℝ (fderiv ℝ f) x-fderiv ℝ (fderiv ℝ g) x‖ ≤ C := by
  constructor
  · rw [← fderiv_sub (hf.differentiableAt (by norm_num)) (hg.differentiableAt (by norm_num)),
      ← norm_iteratedFDeriv_one]
    exact hjets 1 (by norm_num)
  · apply ContinuousLinearMap.opNorm_le_bound _ hC
    intro v
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (norm_nonneg v))
    intro w
    have hn := (iteratedFDeriv ℝ 2 (fun y => f y-g y) x).le_opNorm ![v,w]
    have h := hn.trans (mul_le_mul_of_nonneg_right (hjets 2 le_rfl)
      (Finset.prod_nonneg fun _ _ => norm_nonneg _))
    rw [fun_iteratedFDeriv_sub_apply hf hg] at h
    simpa only [ContinuousMultilinearMap.sub_apply,iteratedFDeriv_two_apply,
      ContinuousLinearMap.sub_apply,Fin.prod_univ_two,Fin.isValue,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.head_cons,mul_assoc] using h

variable {n d N c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × Es

theorem round3_original_actual_adapted_contDiffOn
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep) (F : P × M → Ey)
    (hF : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B F i)
      (incrementsOriginalDifferentiation A B i))
    (i : Fin A.count × Fin c) (e : Ep → OpenPartialHomeomorph M Es)
    (O : Set X) (hTransition : ContDiffOn ℝ ∞ (round3OriginalAdaptedTransition A i.1 e) O)
    (hSource : ∀ z ∈ O, (e z.1).symm z.2 ∈ (A.chart i.1).source)
    (hParameter : ∀ z ∈ O, z.1 ∈ (B i.2).target) :
    ContDiffOn ℝ ∞ (fun w : X => F ((B i.2).symm w.1,(e w.1).symm w.2)) O := by
  let phi := round3OriginalAdaptedTransition A i.1 e
  let f := round3OriginalNativeMapCoordinates A B F i
  let V := (parameterTensorModelEquiv n d) ⁻¹' incrementsOriginalDifferentiation A B i
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
  apply (hf.comp hTransition hMap).congr
  intro w hw
  exact (congrArg (fun x => F ((B i.2).symm w.1,x))
    ((A.chart i.1).left_inv (hSource w hw))).symm

/-- Both actual spatial derivative discrepancies are outputs of the same
original total-joint C2 bound. The cost only sees dimension and the fixed
transition profile through order two. -/
theorem round3_original_C2_actual_spatial_difference
    (T : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j)
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep) (F F0 : P × M → Ey)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (hF : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B F i)
      (incrementsOriginalDifferentiation A B i))
    (hF0 : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B F0 i)
      (incrementsOriginalDifferentiation A B i))
    (hFinite : paperAtlasCj 2 (incrementsOriginalMapCoordinates A B (fun z => F z-F0 z))
      (incrementsOriginalDifferentiation A B) S ≠ ⊤)
    (R : ℝ) (hR0 : 0 ≤ R)
    (hR : (paperAtlasCj 2 (incrementsOriginalMapCoordinates A B (fun z => F z-F0 z))
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
    let f := fun y => F ((B i.2).symm z.1,(e z.1).symm y)
    let f0 := fun y => F0 ((B i.2).symm z.1,(e z.1).symm y)
    ‖fderiv ℝ f z.2-fderiv ℝ f0 z.2‖ ≤ round3OriginalC2AdaptedCost n d N T*R ∧
    ‖fderiv ℝ (fderiv ℝ f) z.2-fderiv ℝ (fderiv ℝ f0) z.2‖ ≤
      round3OriginalC2AdaptedCost n d N T*R := by
  let g := fun w : X => F ((B i.2).symm w.1,(e w.1).symm w.2)
  let g0 := fun w : X => F0 ((B i.2).symm w.1,(e w.1).symm w.2)
  have hg := round3_original_actual_adapted_contDiffOn A B F hF i e O hTransition hSource hParameter
  have hg0 := round3_original_actual_adapted_contDiffOn A B F0 hF0 i e O hTransition hSource hParameter
  have hdiff : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B (fun z => F z-F0 z) i)
      (incrementsOriginalDifferentiation A B i) := fun i => (hF i).sub (hF0 i)
  have hJoint := round3_original_C2_actual_adapted_jets T hT A B (fun z => F z-F0 z)
    S hSO hdiff hFinite R hR0 hR i e O hO hTransition hSource hParameter z hz hSample hChartJets
  have hSliceF : ContDiffAt ℝ 2 (fun y => g (z.1,y)) z.2 :=
    ((hg.contDiffAt (hO.mem_nhds hz)).comp z.2
      (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)
  have hSliceF0 : ContDiffAt ℝ 2 (fun y => g0 (z.1,y)) z.2 :=
    ((hg0.contDiffAt (hO.mem_nhds hz)).comp z.2
      (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)
  apply two_jet_difference_from_iterated _ _ z.2 hSliceF hSliceF0 _
    (mul_nonneg (round3OriginalC2AdaptedCost_nonneg n d N T hT) hR0)
  intro j hj
  exact (norm_iteratedFDeriv_fixed_parameter_slice_le (fun w => g w-g0 w) O hO
    (hg.sub hg0) z.1 z.2 hz j).trans (hJoint j hj)

#print axioms round3_original_C2_actual_spatial_difference
end GlobalEmbedding.Continuation
