import Smoothing.Round3OuterOriginalEllipticityStability

/-! The existing original ellipticity stability proof with its numerical
threshold made literal, before the reference map or any chart choice. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation

def incrementOriginalEllipticityTolerance (n d N : ℕ) (lower : ℝ) : ℝ :=
  (Real.sqrt lower/2)/(actualOriginalMapJetCost n d N 0+1)

theorem incrementOriginalEllipticityTolerance_pos (n d N : ℕ) (lower : ℝ) (hLower : 0 < lower) :
    0 < incrementOriginalEllipticityTolerance n d N lower := by
  have hCost := actualOriginalMapJetCost_nonneg n d N 0
  exact div_pos (div_pos (Real.sqrt_pos.mpr hLower) (by norm_num)) (by positivity)

variable {n d N c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × Es
local notation "Y" => Fin (n+d) → ℝ

variable [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

theorem increment_original_C2_coordinate_ellipticity
    (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (lower : ℝ) (hEll : IncrementsOriginalCoordinateEllipticityInputs Data lower)
    (hF0 : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓘(ℝ,Es)) 𝓘(ℝ,Ey) ∞ Data.F) :
    ∀ (F : P × M → Ey),
    ContMDiff ((𝓘(ℝ,Ep)).prod 𝓘(ℝ,Es)) 𝓘(ℝ,Ey) ∞ F →
    let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet
    paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (fun z => F z-Data.F z))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S ≠ ⊤ →
    (paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (fun z => F z-Data.F z))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S).toReal ≤ incrementOriginalEllipticityTolerance n d N lower →
    IncrementsOriginalCoordinateEllipticityInputs { Data with F := F } (lower/4) := by
  let C := actualOriginalMapJetCost n d N 0
  have hC : 0 ≤ C := actualOriginalMapJetCost_nonneg n d N 0
  let epsilon := incrementOriginalEllipticityTolerance n d N lower
  have hepsilon : 0 < epsilon := incrementOriginalEllipticityTolerance_pos n d N lower hEll.lower_pos
  have hCost : C*epsilon ≤ Real.sqrt lower/2 := by
    calc
      _ ≤ (C+1)*epsilon := mul_le_mul_of_nonneg_right (by linarith) hepsilon.le
      _ = Real.sqrt lower/2 := by
        change (C+1)*((Real.sqrt lower/2)/(C+1)) = Real.sqrt lower/2
        field_simp [ne_of_gt (show 0 < C+1 by linarith)]
  intro F hF S hFinite hBound
  refine ⟨div_pos hEll.lower_pos (by norm_num),?_⟩
  intro p hp a y hy
  obtain ⟨b,hb,hbn⟩ := hd.parameter_cover p hp
  let z : X := (Data.parameterChart b p,y)
  have hNative := (parameterTensorModelEquiv n d).symm_apply_apply z
  have hpz := congrArg Prod.fst hNative
  have hxz := congrArg Prod.snd hNative
  change incrementsOriginalParameterPoint (parameterTensorModelEquiv n d z) = Data.parameterChart b p at hpz
  change incrementsOriginalSourcePoint (parameterTensorModelEquiv n d z) = y at hxz
  have hSample : parameterTensorModelEquiv n d z ∈ S (a,b) := by
    change (_ ∧ _) ∧ _ ∧ _ ∧ _
    rw [hpz,hxz]
    exact ⟨⟨hd.source_norm_subset a hy,(Data.parameterChart b).map_source hb⟩,hy,hbn,
      by simpa only [incrementsOriginalJointPoint,hpz,hxz,(Data.parameterChart b).left_inv hb] using hp⟩
  have hDiff := round3_original_C2_native_first_difference Data.atlas Data.parameterChart F Data.F
    S (fun i y hy => hy.1)
    (round3_original_map_coordinates_contDiffOn Data.atlas Data.parameterChart hd.atlas_smooth hd.parameter_charts_smooth F hF)
    (round3_original_map_coordinates_contDiffOn Data.atlas Data.parameterChart hd.atlas_smooth hd.parameter_charts_smooth Data.F hF0)
    hFinite epsilon hBound (a,b) z hSample
  have hFirst : ‖fderiv ℝ (fun y => F (p,(Data.atlas.chart a).symm y)) y-
      fderiv ℝ (fun y => Data.F (p,(Data.atlas.chart a).symm y)) y‖ ≤ Real.sqrt lower/2 := by
    simpa only [z,(Data.parameterChart b).left_inv hb] using hDiff.trans hCost
  exact actual_first_frame_reserve_perturbation _ _ lower hEll.lower_pos (hEll.lower p hp a y hy) hFirst

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.increment_original_C2_coordinate_ellipticity
