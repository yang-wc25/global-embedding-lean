import Smoothing.Round3OuterC2SpatialDifference
import Probes.ActualOriginalTransverseStability

/-! Uniform actual reference-frame persistence from the ORIGINAL C2 norm.
The tolerance precedes the perturbed map, atlas, chart family and scale.
Both new frame reserves and the actual free-normal normalization margin are
conclusions, with no discrepancy or new-frame premise at the output.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × Es
local notation "𝓙" => 𝓘(ℝ,Es)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}

/-- One original C2 entrance tolerance keeps the same reference packet
usable by the actual perturbed map, including the genuine projected normal.
The original spatial derivatives are obtained internally from the total
joint C2 norm and the actual two-jet of the fixed chart transition. -/
theorem round3_prepared_original_C2_frame_stability
    (T : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j) (cF cT MH : ℝ)
    (hcF : 0 < cF) (hcT : 0 < cT) (hMH : 0 ≤ MH) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀
      (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
      (F0 F : P × M → Ey)
      (hF0 : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (fun x => F0 (p,x)))
      (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (fun x => F (p,x)))
      (S : Fin A.count × Fin c → Set (Fin ((m+1)+d) → ℝ)),
    (∀ i, S i ⊆ incrementsOriginalDifferentiation A B i) →
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B F0 i)
      (incrementsOriginalDifferentiation A B i)) →
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B F i)
      (incrementsOriginalDifferentiation A B i)) →
    paperAtlasCj 2 (incrementsOriginalMapCoordinates A B (fun z => F z-F0 z))
      (incrementsOriginalDifferentiation A B) S ≠ ⊤ →
    (paperAtlasCj 2 (incrementsOriginalMapCoordinates A B (fun z => F z-F0 z))
      (incrementsOriginalDifferentiation A B) S).toReal ≤ epsilon →
    ∀ (i : Fin A.count × Fin c) (e : Ep → OpenPartialHomeomorph M Es)
      (O : Set X), IsOpen O →
    ContDiffOn ℝ ∞ (round3OriginalAdaptedTransition A i.1 e) O →
    (∀ z ∈ O, (e z.1).symm z.2 ∈ (A.chart i.1).source) →
    (∀ z ∈ O, z.1 ∈ (B i.2).target) →
    ∀ (z : X), z ∈ O → z.2 ∈ (e z.1).target →
    e z.1 ∈ IsManifold.maximalAtlas 𝓙 ∞ M →
    parameterTensorModelEquiv (m+1) d (round3OriginalAdaptedTransition A i.1 e z) ∈ S i →
    (∀ j, 1 ≤ j → j ≤ 2 →
      ‖iteratedFDeriv ℝ j (round3OriginalAdaptedTransition A i.1 e) z‖ ≤ T j) →
    let p := (B i.2).symm z.1
    let f0 := fun x => F0 (p,x)
    let f := fun x => F (p,x)
    (∀ v : Es, cF*‖v‖^2 ≤ ‖fderiv ℝ (f0 ∘ (e z.1).symm) z.2 v‖^2) →
    (∀ v : Tdata, cT*‖v‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame f0 (hF0 p) (e z.1).symm z.2 v‖^2) →
    ‖fderiv ℝ (fderiv ℝ (f0 ∘ (e z.1).symm)) z.2‖ ≤ MH →
    (∀ v : Es, (cF/4)*‖v‖^2 ≤ ‖fderiv ℝ (f ∘ (e z.1).symm) z.2 v‖^2) ∧
    (∀ v : Tdata, (cT/4)*‖v‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame f (hF p) (e z.1).symm z.2 v‖^2) := by
  obtain ⟨eta,heta,hStable⟩ := actual_original_selected_frame_uniform_stability
    (m := m) (N := N) (M := M) cF cT MH hcF hcT hMH
  let C := round3OriginalC2AdaptedCost (m+1) d N T
  have hC : 0 ≤ C := round3OriginalC2AdaptedCost_nonneg (m+1) d N T hT
  let epsilon := eta/(C+1)
  have hepsilon : 0 < epsilon := div_pos heta (by positivity)
  have hCost : C*epsilon ≤ eta := by
    calc
      _ ≤ (C+1)*epsilon := mul_le_mul_of_nonneg_right (by linarith) hepsilon.le
      _ = eta := by dsimp [epsilon]; field_simp
  refine ⟨epsilon,hepsilon,?_⟩
  intro A B F0 F hF0 hF S hSO hCoord0 hCoord hFinite hBound i e O hO hTransition
    hSource hParameter z hz heTarget he hSample hChartJets p f0 f hFirst hFrame hHessian
  have hDiff := round3_original_C2_actual_spatial_difference T hT A B F F0 S hSO
    hCoord hCoord0 hFinite epsilon hepsilon.le hBound i e O hO hTransition hSource hParameter
    z hz hSample hChartJets
  apply hStable f0 f (hF0 p) (hF p) (e z.1) he z.2 heTarget
    hFirst hFrame hHessian _ _
  · rw [norm_sub_rev]
    exact hDiff.1.trans hCost
  · exact hDiff.2.trans hCost

#print axioms round3_prepared_original_C2_frame_stability
end GlobalEmbedding.Continuation
