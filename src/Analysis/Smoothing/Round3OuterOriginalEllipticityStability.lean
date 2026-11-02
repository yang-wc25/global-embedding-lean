import Smoothing.Round3OuterC2NativeJets
import Smoothing.Round3OuterOriginalChartPoint
import Probes.ActualSourceRestriction
import Probes.ActualFirstFramePerturbation
import GlobalEmbedding.Paper.IncrementsOriginalImmersionInputs

/-! The actual original coordinate ellipticity of a current map follows from
its fixed reference ellipticity and the original total-joint C2 discrepancy.
The tolerance depends only on the original lower reserve and dimensions;
there is no new-map ellipticity premise or chart-cardinality loss. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation
variable {n d N c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × Es
local notation "Y" => Fin (n+d) → ℝ

theorem round3_original_C2_native_first_difference
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep) (F F0 : P × M → Ey)
    (S : Fin A.count × Fin c → Set Y)
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (hF : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B F i)
      (incrementsOriginalDifferentiation A B i))
    (hF0 : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B F0 i)
      (incrementsOriginalDifferentiation A B i))
    (hFinite : paperAtlasCj 2 (incrementsOriginalMapCoordinates A B (fun z => F z-F0 z))
      (incrementsOriginalDifferentiation A B) S ≠ ⊤)
    (R : ℝ) (hR : (paperAtlasCj 2 (incrementsOriginalMapCoordinates A B (fun z => F z-F0 z))
      (incrementsOriginalDifferentiation A B) S).toReal ≤ R)
    (i : Fin A.count × Fin c) (z : X)
    (hz : parameterTensorModelEquiv n d z ∈ S i) :
    ‖fderiv ℝ (fun y => F ((B i.2).symm z.1,(A.chart i.1).symm y)) z.2-
      fderiv ℝ (fun y => F0 ((B i.2).symm z.1,(A.chart i.1).symm y)) z.2‖ ≤
      actualOriginalMapJetCost n d N 0*R := by
  let V := (parameterTensorModelEquiv n d) ⁻¹' incrementsOriginalDifferentiation A B i
  have hV : IsOpen V := (parameterRound2_originalDifferentiation_open A B i).preimage
    (parameterTensorModelEquiv n d).continuous
  let g := round3OriginalNativeMapCoordinates A B F i
  let g0 := round3OriginalNativeMapCoordinates A B F0 i
  have hg : ContDiffOn ℝ ∞ g V := by
    rw [show g = (EuclideanSpace.equiv (Fin N) ℝ).symm ∘
      incrementsOriginalMapCoordinates A B F i ∘ parameterTensorModelEquiv n d from
      round3_original_native_map_coordinates_eq A B F i]
    exact (EuclideanSpace.equiv (Fin N) ℝ).symm.contDiff.comp_contDiffOn
      ((hF i).comp (parameterTensorModelEquiv n d).contDiff.contDiffOn (fun _ hx => hx))
  have hg0 : ContDiffOn ℝ ∞ g0 V := by
    rw [show g0 = (EuclideanSpace.equiv (Fin N) ℝ).symm ∘
      incrementsOriginalMapCoordinates A B F0 i ∘ parameterTensorModelEquiv n d from
      round3_original_native_map_coordinates_eq A B F0 i]
    exact (EuclideanSpace.equiv (Fin N) ℝ).symm.contDiff.comp_contDiffOn
      ((hF0 i).comp (parameterTensorModelEquiv n d).contDiff.contDiffOn (fun _ hx => hx))
  have hzV : z ∈ V := hSO i hz
  have hf := ((hg.contDiffAt (hV.mem_nhds hzV)).comp z.2
    (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hf0 := ((hg0.contDiffAt (hV.mem_nhds hzV)).comp z.2
    (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  change DifferentiableAt ℝ (fun y => g (z.1,y)) z.2 at hf
  change DifferentiableAt ℝ (fun y => g0 (z.1,y)) z.2 at hf0
  change ‖fderiv ℝ (fun y => g (z.1,y)) z.2-fderiv ℝ (fun y => g0 (z.1,y)) z.2‖ ≤ _
  rw [← fderiv_sub hf hf0,← norm_iteratedFDeriv_one]
  exact (norm_iteratedFDeriv_fixed_parameter_slice_le (fun w => g w-g0 w) V hV
    (hg.sub hg0) z.1 z.2 hzV 1).trans
    (round3_original_C2_native_jets A B (fun w => F w-F0 w) S hSO
      (fun i => (hF i).sub (hF0 i)) hFinite R hR i 1 (by norm_num) z hz)

variable [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

theorem round3_original_map_coordinates_contDiffOn
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (F : P × M → Ey) (hF : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓘(ℝ,Es)) 𝓘(ℝ,Ey) ∞ F)
    (i : Fin A.count × Fin c) :
    ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B F i)
      (incrementsOriginalDifferentiation A B i) := by
  have hh := hF.comp_contMDiffOn (round3_original_jointPoint_contMDiffOn A B hA hB i)
  exact (EuclideanSpace.equiv (Fin N) ℝ).contDiff.comp_contDiffOn hh.contDiffOn

theorem round3_original_C2_coordinate_ellipticity
    (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (lower : ℝ) (hEll : IncrementsOriginalCoordinateEllipticityInputs Data lower)
    (hF0 : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓘(ℝ,Es)) 𝓘(ℝ,Ey) ∞ Data.F) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ (F : P × M → Ey),
    ContMDiff ((𝓘(ℝ,Ep)).prod 𝓘(ℝ,Es)) 𝓘(ℝ,Ey) ∞ F →
    let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet
    paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (fun z => F z-Data.F z))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S ≠ ⊤ →
    (paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (fun z => F z-Data.F z))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S).toReal ≤ epsilon →
    IncrementsOriginalCoordinateEllipticityInputs { Data with F := F } (lower/4) := by
  let C := actualOriginalMapJetCost n d N 0
  have hC : 0 ≤ C := actualOriginalMapJetCost_nonneg n d N 0
  let epsilon := (Real.sqrt lower/2)/(C+1)
  have hepsilon : 0 < epsilon := div_pos (div_pos (Real.sqrt_pos.mpr hEll.lower_pos) (by norm_num)) (by positivity)
  have hCost : C*epsilon ≤ Real.sqrt lower/2 := by
    calc
      _ ≤ (C+1)*epsilon := mul_le_mul_of_nonneg_right (by linarith) hepsilon.le
      _ = Real.sqrt lower/2 := by dsimp [epsilon]; field_simp
  refine ⟨epsilon,hepsilon,?_⟩
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

#print axioms round3_original_C2_native_first_difference
#print axioms round3_original_map_coordinates_contDiffOn
#print axioms round3_original_C2_coordinate_ellipticity
end GlobalEmbedding.Continuation
