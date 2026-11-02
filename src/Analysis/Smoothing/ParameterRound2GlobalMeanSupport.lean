import Smoothing.ParameterRound2GlobalObservedDifference

/-! Genuine inactive primary zero germs for the SAME global observed
leading and error coefficients. The proof uses only original cutoff
supports and each subordinate chart's source locality. It never requires
positivity, phase smoothness, or normal smoothness on inactive labels. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

theorem parameterRound2_actual_globalObserved_inactive_germ
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) (W : Set (Ep × M)) (hW : IsOpen W) (ν : Λ)
    (hsupport : ∀ β, incrementsGlobalRelativeSupport W
      (fun z => g.eta ν β z*g.cutoff ν z) ⊆ (g.chart ν β).source)
    (hinverse : ∀ β z, z ∈ (g.chart ν β).target →
      (g.chart ν β).symm z = (z.1,g.inverse ν β z.1 z.2))
    (e : OpenPartialHomeomorph M D) (Omega : Set X) (hOmega : IsOpen Omega)
    (hkappa : ContinuousOn (fun z : X => (z.1,e.symm z.2)) Omega)
    (hmap : MapsTo (fun z : X => (z.1,e.symm z.2)) Omega W)
    (x : X) (hx : x ∈ Omega)
    (hinactive : (x.1,e.symm x.2) ∉ incrementsGlobalRelativeSupport W (g.cutoff ν)) :
    (fun z : X => incrementsGlobalObservedLeading F g input e z.1 z.2 ν) =ᶠ[𝓝 x] 0 ∧
    (fun z : X => incrementsGlobalObservedError F hF g input length tau e z.1 z.2 ν) =ᶠ[𝓝 x] 0 := by
  let kappa := fun z : X => (z.1,e.symm z.2)
  have hnot (z : X) (hz : z ∈ Omega)
      (hn : kappa z ∉ incrementsGlobalRelativeSupport W (g.cutoff ν)) :
      kappa z ∉ tsupport (g.cutoff ν) := by
    intro ht
    apply hn
    rw [parameterRound2_global_relativeSupport_eq W hW]
    exact ⟨hmap hz,ht⟩
  have hpoint (z : X) (hz : z ∈ Omega)
      (hn : kappa z ∉ incrementsGlobalRelativeSupport W (g.cutoff ν)) :
      incrementsGlobalObservedLeading F g input e z.1 z.2 ν = 0 ∧
      incrementsGlobalObservedError F hF g input length tau e z.1 z.2 ν = 0 := by
    have hcont := hkappa.continuousAt (hOmega.mem_nhds hz)
    have hCutZero : (fun w : X => g.cutoff ν (kappa w)) =ᶠ[𝓝 z] 0 :=
      hcont.tendsto.eventually (notMem_tsupport_iff_eventuallyEq.mp (hnot z hz hn))
    have hbZero : (fun w : X => incrementsGlobalPrimaryB F g input ν (kappa w)) =ᶠ[𝓝 z] 0 := by
      filter_upwards [hCutZero] with w hw
      simp only [incrementsGlobalPrimaryB,hw,Pi.zero_apply,zero_mul]
    have hsub (β : Β) : incrementsGlobalRelativeSupport W (fun w => g.eta ν β w*g.cutoff ν w) ⊆
        incrementsGlobalRelativeSupport W (g.cutoff ν) := by
      rw [parameterRound2_global_relativeSupport_eq W hW,
        parameterRound2_global_relativeSupport_eq W hW]
      exact Set.inter_subset_inter_right W tsupport_mul_subset_right
    have hcorrZero (ch : Bool) (β : Β) :
        (fun w : X => parameterRound2_globalCorrection F hF g input length tau ch ν β (kappa w)) =ᶠ[𝓝 z] 0 := by
      exact parameterRound2_relative_observation_zero_germ
        (parameterRound2_globalCorrection F hF g input length tau ch ν β) W
        (incrementsGlobalRelativeSupport W (fun w => g.eta ν β w*g.cutoff ν w)) hW
        (parameterRound2_globalCorrection_relative_support F hF g input length tau ch ν β W hW
          (hsupport β) (hinverse β)) kappa z hcont (hmap hz) (fun h => hn (hsub β h))
    have hslic : Tendsto (fun y : D => (z.1,y)) (𝓝 z.2) (𝓝 z) :=
      (continuous_const.prodMk continuous_id).continuousAt.tendsto
    have hbSlice : (fun y : D => incrementsGlobalPrimaryB F g input ν (z.1,e.symm y)) =ᶠ[𝓝 z.2] 0 :=
      hbZero.comp_tendsto hslic
    have hcorrSlice (ch : Bool) (β : Β) :
        (fun y : D => parameterRound2_globalCorrection F hF g input length tau ch ν β
          (z.1,e.symm y)) =ᶠ[𝓝 z.2] 0 := (hcorrZero ch β).comp_tendsto hslic
    have hbD : fderiv ℝ (fun y : D => incrementsGlobalPrimaryB F g input ν (z.1,e.symm y)) z.2 = 0 := by
      simpa using hbSlice.fderiv_eq (𝕜 := ℝ)
    have hcD (ch : Bool) (β : Β) : fderiv ℝ
        (fun y : D => parameterRound2_globalCorrection F hF g input length tau ch ν β (z.1,e.symm y)) z.2 = 0 := by
      simpa using (hcorrSlice ch β).fderiv_eq (𝕜 := ℝ)
    refine ⟨?_,?_⟩
    · ext r coord
      simp [incrementsGlobalObservedLeading,incrementsLeadingCoefficient,hbSlice.eq_of_nhds]
    · ext r coord
      have he : incrementsPrimaryErrorCoefficient 1 tau
        (fun y : D => incrementsGlobalPrimaryB F g input ν (z.1,e.symm y))
        (fun y : D => g.phase ν (z.1,e.symm y)) (fun y : D => g.normal ν (z.1,e.symm y))
        (fun β y => parameterRound2_globalCorrection F hF g input length tau true ν β (z.1,e.symm y))
        (fun β y => parameterRound2_globalCorrection F hF g input length tau false ν β (z.1,e.symm y))
        z.2 (EuclideanSpace.single r 1) coord = 0 := by
        simp [incrementsPrimaryErrorCoefficient,incrementsPrimaryDerivativeCoefficient,hbD,hbSlice.eq_of_nhds,
          hcD,fun ch β => (hcorrSlice ch β).eq_of_nhds]
      simpa only [incrementsGlobalObservedError,parameterRound2_globalCorrection,
        Bool.false_eq_true,ite_false,ite_true,sub_zero,Pi.zero_apply] using he
  have hneigh : ∀ᶠ z in 𝓝 x, z ∈ Omega ∧ kappa z ∉ incrementsGlobalRelativeSupport W (g.cutoff ν) := by
    filter_upwards [hOmega.mem_nhds hx,
      (hkappa.continuousAt (hOmega.mem_nhds hx)).eventually
        ((isClosed_tsupport (g.cutoff ν)).isOpen_compl.mem_nhds (hnot x hx hinactive))] with z hz hn
    exact ⟨hz,fun h => hn ((parameterRound2_global_relativeSupport_eq W hW (g.cutoff ν)) ▸ h).2⟩
  exact ⟨hneigh.mono (fun z hz => (hpoint z hz.1 hz.2).1),
    hneigh.mono (fun z hz => (hpoint z hz.1 hz.2).2)⟩

#print axioms parameterRound2_actual_globalObserved_inactive_germ
end GlobalEmbedding.Continuation
