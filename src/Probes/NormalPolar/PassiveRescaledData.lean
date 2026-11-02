import NormalPolar.PassiveRescaledTransverse
import GlobalEmbedding.Paper.IncrementsOriginalImmersionInputs
import GlobalEmbedding.Paper.IncrementsOriginalQualitativeAdmissibility

/-! The actual rescaled original input changes only F to c F. All source
and parameter charts, original norm samples, phases, normal values and
tensor data retain their literal definitions. A single quarter of the
original coordinate ellipticity works throughout c >= 1/2. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace P]
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

def passiveRescaledData (Data : IncrementsOriginalNativeData n d N M P) (c : ℝ) :
    IncrementsOriginalNativeData n d N M P :=
  { Data with F := c • Data.F }

variable [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

theorem passiveRescaledData_domains (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (c : ℝ) :
    IncrementsOriginalDomainConditions (passiveRescaledData Data c) := by
  cases hd
  constructor <;> assumption

theorem passiveRescaledData_smooth (Data : IncrementsOriginalNativeData n d N M P)
    (hs : IncrementsOriginalSmoothInputs Data) (c : ℝ) :
    IncrementsOriginalSmoothInputs (passiveRescaledData Data c) := by
  have hconst : ContMDiffOn ((𝓘(ℝ,EuclideanSpace ℝ (Fin d))).prod IM) 𝓘(ℝ,ℝ) ∞
      (fun _ : P × M => c) (incrementsOriginalParameterRegion Data) := contMDiffOn_const
  exact { hs with F_joint := hconst.smul hs.F_joint }

theorem passiveRescaledData_immersion (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hi : IncrementsOriginalSliceImmersionInputs Data) (c : ℝ) (hc : c ≠ 0) :
    IncrementsOriginalSliceImmersionInputs (passiveRescaledData Data c) where
  immersion := fun p hp x =>
    (immersion_const_rescale_iff (fun y => Data.F (p,y))
      (incrementsOriginal_slice_contMDiff Data hd hs p hp) c hc x).mpr (hi.immersion p hp x)

theorem passiveRescaledData_ellipticity (Data : IncrementsOriginalNativeData n d N M P)
    (cF : ℝ) (he : IncrementsOriginalCoordinateEllipticityInputs Data cF)
    (c : ℝ) (hc : 1/2 ≤ c) :
    IncrementsOriginalCoordinateEllipticityInputs (passiveRescaledData Data c) (cF/4) := by
  refine ⟨div_pos he.lower_pos (by norm_num),?_⟩
  intro p hp i y hy v
  change Fin Data.atlas.count at i
  change y ∈ Data.sourceNormDomain i at hy
  change p ∈ Data.parameterSet at hp
  have hb := he.lower p hp i y hy v
  have hc0 : 0 < c := by linarith
  change (cF/4)*‖v‖^2 ≤ ‖fderiv ℝ (c • (fun z => Data.F (p,(Data.atlas.chart i).symm z))) y v‖^2
  rw [fderiv_const_smul_field]
  simp only [Pi.smul_apply,ContinuousLinearMap.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_pos hc0]
  have hc2 : (1/4 : ℝ) ≤ c^2 := by nlinarith
  have hscale := mul_le_mul_of_nonneg_right hc2
    (sq_nonneg ‖fderiv ℝ (fun z => Data.F (p,(Data.atlas.chart i).symm z)) y v‖)
  nlinarith

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.passiveRescaledData_smooth
#print axioms GlobalEmbedding.Continuation.passiveRescaledData_immersion
#print axioms GlobalEmbedding.Continuation.passiveRescaledData_ellipticity
