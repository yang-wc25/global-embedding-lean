import Probes.ActualIncrementOriginalOpenCore

/-! A total family of spatially smooth slices for the actual parameter-open
data. Every valid parameter uses exactly the original native F on ALL spatial
points. Invalid parameters select the zero slice. Joint smoothness is asserted
only on the original open coordinate region, never across its boundary. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff ENNReal Topology
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × Es

def actualOriginalOpenParameterSlice
    (D : IncrementsOriginalNativeData n d N M P)
    (i : Fin D.atlas.count × Fin D.parameterCount) (p : Ep) (x : M) : V := by
  classical
  exact if (D.parameterChart i.2).symm p ∈ D.parameterOpen then
    D.F ((D.parameterChart i.2).symm p,x) else 0

theorem actualOriginalOpenParameterSlice_eq
    (D : IncrementsOriginalNativeData n d N M P)
    (i : Fin D.atlas.count × Fin D.parameterCount) (p : Ep)
    (hp : (D.parameterChart i.2).symm p ∈ D.parameterOpen) :
    actualOriginalOpenParameterSlice D i p = actualOriginalParameterSlice D i p := by
  funext x
  simp only [actualOriginalOpenParameterSlice,if_pos hp,actualOriginalParameterSlice]

theorem actualOriginalOpenParameterSlice_contMDiff
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D) (hs : IncrementsOriginalSmoothInputs D)
    (i : Fin D.atlas.count × Fin D.parameterCount) (p : Ep) :
    ContMDiff 𝓘(ℝ,Es) 𝓘(ℝ,V) ∞ (actualOriginalOpenParameterSlice D i p) := by
  by_cases hp : (D.parameterChart i.2).symm p ∈ D.parameterOpen
  · rw [actualOriginalOpenParameterSlice_eq D i p hp]
    exact incrementsOriginal_slice_contMDiff D hd hs _ hp
  · have hz : actualOriginalOpenParameterSlice D i p = fun _ : M => (0 : V) := by
      funext x
      simp only [actualOriginalOpenParameterSlice,if_neg hp]
    rw [hz]
    exact contMDiff_const

theorem actualOriginalOpenParameterSlice_native_eqOn
    (D : IncrementsOriginalNativeData n d N M P)
    (i : Fin D.atlas.count × Fin D.parameterCount) :
    EqOn (fun z : X => actualOriginalOpenParameterSlice D i z.1 ((D.atlas.chart i.1).symm z.2))
      (actualOriginalNativeMap D i) (actualOriginalNativeOpen D i) := by
  intro z hz
  change actualOriginalOpenParameterSlice D i z.1 ((D.atlas.chart i.1).symm z.2) = _
  rw [actualOriginalOpenParameterSlice_eq D i z.1 (actualOriginalNativeOpen_parameter D i hz)]
  rfl

theorem actualOriginalOpenParameterSlice_native_contDiffOn
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D) (hs : IncrementsOriginalSmoothInputs D)
    (i : Fin D.atlas.count × Fin D.parameterCount) :
    ContDiffOn ℝ ∞
      (fun z : X => actualOriginalOpenParameterSlice D i z.1 ((D.atlas.chart i.1).symm z.2))
      (actualOriginalNativeOpen D i) :=
  (actualOriginalNativeMap_contDiffOn_parameter_open D hd hs i).congr
    (actualOriginalOpenParameterSlice_native_eqOn D i)

/-- Original base-two Core at order j already supplies first jets through j+1
and Hessian jets through j. The extra first order uses ell ≤ 1 and costs no
additional original profile order or negative power of ell. -/
theorem actual_original_open_slice_core_profiles
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D) (hs : IncrementsOriginalSmoothInputs D)
    (j : ℕ) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hfinite : incrementsOriginalCoreInputProfile D j ell ≠ ⊤)
    (budget : ℝ) (hbudget : (incrementsOriginalCoreInputProfile D j ell).toReal ≤ budget)
    (i : Fin D.atlas.count × Fin D.parameterCount) :
    let O := actualOriginalNativeOpen D i
    let S := (parameterTensorModelEquiv n d) ⁻¹'
      incrementsOriginalEvaluation D.atlas D.parameterChart
        D.sourceNormDomain D.parameterNormDomain D.parameterSet i
    let F := actualOriginalOpenParameterSlice D i
    let C := actualOriginalMapJetCost n d N j*budget
    (ContDiffOn ℝ ∞ (fun z : X => fderiv ℝ (F z.1 ∘ (D.atlas.chart i.1).symm) z.2) O ∧
      ∀ k ≤ j+1, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k
        (fun y : X => fderiv ℝ (F y.1 ∘ (D.atlas.chart i.1).symm) y.2) z‖ ≤ C) ∧
    (ContDiffOn ℝ ∞ (fun z : X => fderiv ℝ (fderiv ℝ (F z.1 ∘ (D.atlas.chart i.1).symm)) z.2) O ∧
      ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k
        (fun y : X => fderiv ℝ (fderiv ℝ (F y.1 ∘ (D.atlas.chart i.1).symm)) y.2) z‖ ≤ C) := by
  intro O S F C
  let f : X → V := fun z => F z.1 ((D.atlas.chart i.1).symm z.2)
  have hO : IsOpen O := actualOriginalNativeOpen_isOpen D hd i
  have hSO : S ⊆ O := actualOriginalNativeOpen_evaluation_subset D hd i
  have hf : ContDiffOn ℝ ∞ f O := actualOriginalOpenParameterSlice_native_contDiffOn D hd hs i
  have hC : 0 ≤ C := mul_nonneg (actualOriginalMapJetCost_nonneg n d N j)
    (ENNReal.toReal_nonneg.trans hbudget)
  have hb : ∀ k ≤ j, ∀ b ≤ 2, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ (k+b) f z‖ ≤ C := by
    intro k hk b hbb z hz
    have heq : f =ᶠ[𝓝 z] actualOriginalNativeMap D i :=
      Filter.eventuallyEq_of_mem (hO.mem_nhds (hSO hz)) (actualOriginalOpenParameterSlice_native_eqOn D i)
    rw [(heq.iteratedFDeriv ℝ (k+b)).eq_of_nhds]
    exact (actual_original_parameter_open_core_shifted_jets D hd hs j ell hell hfinite i hk hbb hz).trans
      (mul_le_mul_of_nonneg_left hbudget (actualOriginalMapJetCost_nonneg n d N j))
  have hp := actual_spatial_first_second_slow_jets f O S hO hSO hf j ell C hell.le hb
  refine ⟨⟨hp.1.1,?_⟩,hp.2⟩
  intro k hk z hz
  by_cases hkj : k ≤ j
  · exact hp.1.2 k hkj z hz
  · have he : k = j+1 := by omega
    subst k
    calc
      _ ≤ ell^(j+1)*‖iteratedFDeriv ℝ ((j+1)+1) f z‖ :=
        mul_le_mul_of_nonneg_left (spatial_first_jet_le hO hf (hSO hz) (j+1))
          (pow_nonneg hell.le _)
      _ = ell*(ell^j*‖iteratedFDeriv ℝ (j+2) f z‖) := by rw [pow_succ]; ring
      _ ≤ ell*C := mul_le_mul_of_nonneg_left (hb j le_rfl 2 le_rfl z hz) hell.le
      _ ≤ C := mul_le_of_le_one_left hC hell1

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualOriginalOpenParameterSlice_contMDiff
#print axioms GlobalEmbedding.Continuation.actualOriginalOpenParameterSlice_native_eqOn
#print axioms GlobalEmbedding.Continuation.actual_original_open_slice_core_profiles
