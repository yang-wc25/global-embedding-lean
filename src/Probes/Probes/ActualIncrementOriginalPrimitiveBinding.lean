import Probes.ActualIncrementOriginalPrimaryFamily
import GlobalEmbedding.Paper.IncrementsOriginalDecompositionInputs

/-! Literal original qualitative inputs in the true parameter chart. These
are used to fill the actual global mean primitive record, with relative
supports transported through the actual parameter-chart inverse. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "𝓙" => 𝓘(ℝ,Es)

theorem actual_original_parameter_pullback_smooth
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (Data : IncrementsOriginalNativeData n d N M P) (hd : IncrementsOriginalDomainConditions Data)
    (ip : Fin Data.parameterCount) (f : P × M → Y) (R : Set (P × M))
    (hf : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Y) ∞ f R)
    (U : Set (Ep × M)) (htarget : ∀ z ∈ U, z.1 ∈ (Data.parameterChart ip).target)
    (hmap : MapsTo (fun z : Ep × M => ((Data.parameterChart ip).symm z.1,z.2)) U R) :
    ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Y) ∞
      (fun z : Ep × M => f ((Data.parameterChart ip).symm z.1,z.2)) U := by
  have hp := contMDiffOn_symm_of_mem_maximalAtlas (hd.parameter_charts_smooth ip)
  have hr : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) ((𝓘(ℝ,Ep)).prod 𝓙) ∞
      (fun z : Ep × M => ((Data.parameterChart ip).symm z.1,z.2)) U :=
    (hp.comp contMDiff_fst.contMDiffOn htarget).prodMk contMDiffOn_snd
  exact hf.comp hr hmap

theorem actual_original_parameter_pullback_support
    (Data : IncrementsOriginalNativeData n d N M P) (ip : Fin Data.parameterCount)
    (W : Set (Ep × M))
    (htarget : ∀ z ∈ W, z.1 ∈ (Data.parameterChart ip).target)
    (hregion : ∀ z ∈ W, ((Data.parameterChart ip).symm z.1,z.2) ∈
      incrementsOriginalParameterRegion Data)
    (nu : Fin Data.primaryCount) :
    ∀ z ∈ incrementsGlobalRelativeSupport W
      (fun z : Ep × M => Data.cutoff nu ((Data.parameterChart ip).symm z.1,z.2)),
      ((Data.parameterChart ip).symm z.1,z.2) ∈ incrementsOriginalRelativeCutoffSupport Data nu := by
  let rho : W → incrementsOriginalParameterRegion Data := fun z =>
    ⟨((Data.parameterChart ip).symm z.val.1,z.val.2),hregion z.val z.property⟩
  have hrho : Continuous rho := by
    apply Continuous.subtype_mk
    exact continuousOn_iff_continuous_domRestrict.mp (((Data.parameterChart ip).continuousOn_symm.comp
      continuousOn_fst htarget).prodMk continuousOn_snd)
  intro z hz
  obtain ⟨w,hw,rfl⟩ := hz
  have hs := tsupport_comp_subset_preimage
    (fun y : incrementsOriginalParameterRegion Data => Data.cutoff nu y.val) hrho hw
  exact ⟨rho w,hs,rfl⟩

theorem actual_original_phase_mdifferentiableAt
    (Data : IncrementsOriginalNativeData n d N M P) (hd : IncrementsOriginalDomainConditions Data)
    (hs : IncrementsOriginalSmoothInputs Data) (nu : Fin Data.primaryCount)
    (p : P) (x : M) (hz : (p,x) ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data) :
    MDifferentiableAt 𝓙 𝓘(ℝ,ℝ) (fun y => Data.phase nu (p,y)) x := by
  have hO : IsOpen (Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data) :=
    (hd.primary_open nu).inter (hd.parameter_open.prod isOpen_univ)
  have hh := ((hs.phase_joint nu).contMDiffAt (hO.mem_nhds hz)).comp x
    (contMDiff_const.prodMk contMDiff_id).contMDiffAt
  exact hh.mdifferentiableAt (by simp)

theorem actual_original_phase_sum_covector
    (Data : IncrementsOriginalNativeData n d N M P) (hd : IncrementsOriginalDomainConditions Data)
    (hs : IncrementsOriginalSmoothInputs Data) (nu mu : Fin Data.primaryCount)
    (p : P) (x : M)
    (hnu : (p,x) ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data)
    (hmu : (p,x) ∈ Data.primaryDomain mu ∩ incrementsOriginalParameterRegion Data) :
    (tangentSpaceCastModel 𝓘(ℝ,ℝ) (Data.phase nu (p,x)+Data.phase mu (p,x))).toContinuousLinearMap.comp
      (mfderiv 𝓙 𝓘(ℝ,ℝ) (fun y => Data.phase nu (p,y)+Data.phase mu (p,y)) x) =
        incrementsOriginalPhaseCovector Data nu p x + incrementsOriginalPhaseCovector Data mu p x := by
  have hn := actual_original_phase_mdifferentiableAt Data hd hs nu p x hnu
  have hm := actual_original_phase_mdifferentiableAt Data hd hs mu p x hmu
  exact mfderiv_add hn hm

theorem actual_original_phase_sub_covector
    (Data : IncrementsOriginalNativeData n d N M P) (hd : IncrementsOriginalDomainConditions Data)
    (hs : IncrementsOriginalSmoothInputs Data) (nu mu : Fin Data.primaryCount)
    (p : P) (x : M)
    (hnu : (p,x) ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data)
    (hmu : (p,x) ∈ Data.primaryDomain mu ∩ incrementsOriginalParameterRegion Data) :
    (tangentSpaceCastModel 𝓘(ℝ,ℝ) (Data.phase nu (p,x)-Data.phase mu (p,x))).toContinuousLinearMap.comp
      (mfderiv 𝓙 𝓘(ℝ,ℝ) (fun y => Data.phase nu (p,y)-Data.phase mu (p,y)) x) =
        incrementsOriginalPhaseCovector Data nu p x - incrementsOriginalPhaseCovector Data mu p x := by
  have hn := actual_original_phase_mdifferentiableAt Data hd hs nu p x hnu
  have hm := actual_original_phase_mdifferentiableAt Data hd hs mu p x hmu
  exact mfderiv_sub hn hm

theorem actual_original_parameter_decomposition
    (Data : IncrementsOriginalNativeData n d N M P) (ip : Fin Data.parameterCount)
    (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (z : Ep × M)
    (hdecomp : input ((Data.parameterChart ip).symm z.1) z.2 =
      incrementsOriginalDecompositionTensor Data ((Data.parameterChart ip).symm z.1) z.2
        (input ((Data.parameterChart ip).symm z.1) z.2))
    (v w : TangentSpace 𝓙 z.2) :
    (∑ nu, (Data.cutoff nu ((Data.parameterChart ip).symm z.1,z.2) *
        Real.sqrt (Data.linearArgument nu ((Data.parameterChart ip).symm z.1) z.2
          (input ((Data.parameterChart ip).symm z.1) z.2)))^2 *
      incrementsGlobalScalarDerivative (I := 𝓙)
        (fun y : Ep × M => Data.phase nu ((Data.parameterChart ip).symm y.1,y.2)) z v *
      incrementsGlobalScalarDerivative (I := 𝓙)
        (fun y : Ep × M => Data.phase nu ((Data.parameterChart ip).symm y.1,y.2)) z w) =
      input ((Data.parameterChart ip).symm z.1) z.2 v w := by
  have hh := congrArg (fun A : LinearMap.BilinForm ℝ (TangentSpace 𝓙 z.2) => A v w) hdecomp
  simp only [incrementsOriginalDecompositionTensor,LinearMap.sum_apply,LinearMap.smul_apply,
    incrementsOriginalPhaseSquare,LinearMap.BilinForm.comp_apply,LinearMap.mul_apply',smul_eq_mul] at hh
  simpa only [incrementsGlobalScalarDerivative,incrementsOriginalPhaseCovector,
    ContinuousLinearMap.coe_coe,mul_assoc] using hh.symm

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_parameter_pullback_support
#print axioms GlobalEmbedding.Continuation.actual_original_phase_sum_covector
#print axioms GlobalEmbedding.Continuation.actual_original_phase_sub_covector
#print axioms GlobalEmbedding.Continuation.actual_original_parameter_decomposition
