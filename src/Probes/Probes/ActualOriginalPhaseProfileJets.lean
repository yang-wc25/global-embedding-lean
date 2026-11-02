import Probes.ActualOriginalGivenProfile
import Smoothing.WeightedActualOperations

/-! Original total phase-differential coordinates supply the actual joint
positive-order phase jets. The constant contains only fixed model/operator
factors. The estimate uses the original compact parameter samples and actual
open smooth neighborhood; no phase value, produced chart budget, or global
smoothness outside the original parameter region is assumed. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff ENNReal Topology BigOperators
namespace GlobalEmbedding.Continuation

def actualScalarCovectorAssembly (a : ℕ) :
    (Fin a → ℝ) →L[ℝ] ((Fin a → ℝ) →L[ℝ] ℝ) :=
  ∑ r, (ContinuousLinearMap.proj r : (Fin a → ℝ) →L[ℝ] ℝ).smulRight
    (ContinuousLinearMap.proj r : (Fin a → ℝ) →L[ℝ] ℝ)

theorem actualScalarCovectorAssembly_exact (a : ℕ) (L : (Fin a → ℝ) →L[ℝ] ℝ) :
    actualScalarCovectorAssembly a (fun r => L (Pi.single r 1)) = L := by
  ext v
  have hv : (∑ r : Fin a, v r • (Pi.single r 1 : Fin a → ℝ)) = v := by
    ext s
    simp [Pi.single_apply]
  calc
    _ = ∑ r : Fin a, L (Pi.single r 1)*v r := by simp [actualScalarCovectorAssembly]
    _ = L (∑ r : Fin a, v r • (Pi.single r 1 : Fin a → ℝ)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [map_smul]
      change _ = v r*L (Pi.single r 1)
      ring
    _ = _ := congrArg L hv

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "X" => Ep × Es

private local instance phaseProfileProductCharted : ChartedSpace X (P × M) :=
  prodChartedSpace Ep P Es M
private local instance phaseProfileProductManifold : IsManifold 𝓘(ℝ,X) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,Es)) (n := ∞) P M

def actualOriginalPhaseOpen (D : IncrementsOriginalNativeData n d N M P)
    (nu : Fin D.primaryCount) (i : Fin D.atlas.count × Fin D.parameterCount) :
    Set (Fin (n+d) → ℝ) :=
  incrementsOriginalPrimaryDifferentiation D nu i ∩
    (incrementsOriginalDifferentiation D.atlas D.parameterChart i ∩
      (incrementsOriginalJointPoint D.atlas D.parameterChart i) ⁻¹'
        incrementsOriginalParameterRegion D)

omit [IsManifold 𝓘(ℝ,Ep) ∞ P] in
theorem actualOriginalPhaseOpen_open
    (D : IncrementsOriginalNativeData n d N M P) (hd : IncrementsOriginalDomainConditions D)
    (nu : Fin D.primaryCount) (i : Fin D.atlas.count × Fin D.parameterCount) :
    IsOpen (actualOriginalPhaseOpen D nu i) :=
  (actual_original_primaryDifferentiation_open D hd.primary_open nu i).inter
    (actual_original_parameter_coordinate_region_open D hd.parameter_open i)

omit [IsManifold 𝓘(ℝ,Ep) ∞ P] in
theorem actualOriginalPhaseOpen_sample
    (D : IncrementsOriginalNativeData n d N M P) (hd : IncrementsOriginalDomainConditions D)
    (nu : Fin D.primaryCount) (i : Fin D.atlas.count × Fin D.parameterCount) :
    incrementsOriginalPrimaryEvaluation D nu i ⊆ actualOriginalPhaseOpen D nu i := by
  intro y hy
  exact ⟨⟨hy.1.1,hy.2⟩,hy.1.1,hd.parameter_subset hy.1.2.2.2,mem_univ _⟩

theorem actualOriginalJointPhase_contDiffOn
    (D : IncrementsOriginalNativeData n d N M P) (hd : IncrementsOriginalDomainConditions D)
    (hs : IncrementsOriginalSmoothInputs D) (nu : Fin D.primaryCount)
    (i : Fin D.atlas.count × Fin D.parameterCount) :
    ContDiffOn ℝ ∞ (actualOriginalJointPhase D nu i) (actualOriginalPhaseOpen D nu i) := by
  let e := (D.parameterChart i.2).prod (D.atlas.chart i.1)
  let a := parameterTensorModelEquiv n d
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ,X) ∞ (P × M) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.mem_maximalAtlas_prod (hd.parameter_charts_smooth i.2)
      (hd.atlas_smooth.chart_mem i.1)
  have hphase : ContMDiffOn 𝓘(ℝ,X) 𝓘(ℝ,ℝ) ∞ (D.phase nu)
      (D.primaryDomain nu ∩ incrementsOriginalParameterRegion D) := by
    rw [modelWithCornersSelf_prod]
    exact hs.phase_joint nu
  let : ChartedSpace X X := chartedSpaceSelf X
  have hi : ContMDiffOn 𝓘(ℝ,X) 𝓘(ℝ,X) ∞ e.symm e.target :=
    contMDiffOn_symm_of_mem_maximalAtlas he
  have hnative : ContDiffOn ℝ ∞ (D.phase nu ∘ e.symm)
      (e.target ∩ e.symm ⁻¹' (D.primaryDomain nu ∩ incrementsOriginalParameterRegion D)) :=
    (hphase.comp (hi.mono inter_subset_left) (fun _ hx => hx.2)).contDiffOn
  apply hnative.comp a.symm.contDiff.contDiffOn
  intro y hy
  exact ⟨⟨hy.1.1.2,hy.1.1.1⟩,hy.1.2,hy.2.2⟩

theorem actualOriginalTotalPhaseCoordinates_contDiffOn
    (D : IncrementsOriginalNativeData n d N M P) (hd : IncrementsOriginalDomainConditions D)
    (hs : IncrementsOriginalSmoothInputs D) (nu : Fin D.primaryCount)
    (i : Fin D.atlas.count × Fin D.parameterCount) :
    ContDiffOn ℝ ∞ (actualOriginalTotalPhaseCoordinates D nu i) (actualOriginalPhaseOpen D nu i) := by
  apply contDiffOn_pi.mpr
  intro r
  exact ((actualOriginalJointPhase_contDiffOn D hd hs nu i).fderiv_of_isOpen
    (actualOriginalPhaseOpen_open D hd nu i) (m := ∞) (by simp)).clm_apply contDiffOn_const

def actualOriginalTotalPhaseJetCost (n d j : ℕ) : ℝ :=
  linearModelFactor (parameterTensorModelEquiv n d) (j+1)*
    ‖actualScalarCovectorAssembly (n+d)‖*coordinateDimensionFactor (n+d) j

theorem actual_original_given_phase_positive_jets
    (D : IncrementsOriginalNativeData n d N M P) (hd : IncrementsOriginalDomainConditions D)
    (hs : IncrementsOriginalSmoothInputs D) (j : ℕ) (ell budget : ℝ) (hell : 0 < ell)
    (hfinite : actualOriginalGivenInputProfile D j ell ≠ ⊤)
    (hbudget : (actualOriginalGivenInputProfile D j ell).toReal ≤ budget)
    (nu : Fin D.primaryCount) (i : Fin D.atlas.count × Fin D.parameterCount)
    (k : ℕ) (hk : k ≤ j) (z : X)
    (hz : parameterTensorModelEquiv n d z ∈ incrementsOriginalPrimaryEvaluation D nu i) :
    ell^k*‖iteratedFDeriv ℝ (k+1)
      (actualOriginalJointPhase D nu i ∘ parameterTensorModelEquiv n d) z‖ ≤
        actualOriginalTotalPhaseJetCost n d j*budget := by
  let O := incrementsOriginalPrimaryDifferentiation D nu
  let U := actualOriginalPhaseOpen D nu
  let S := incrementsOriginalPrimaryEvaluation D nu
  let f := actualOriginalTotalPhaseCoordinates D nu
  let a := parameterTensorModelEquiv n d
  have hO (i) := actual_original_primaryDifferentiation_open D hd.primary_open nu i
  have hU (i) := actualOriginalPhaseOpen_open D hd nu i
  have hSU (i) := actualOriginalPhaseOpen_sample D hd nu i
  have hf (i) := actualOriginalTotalPhaseCoordinates_contDiffOn D hd hs nu i
  have hle := actualOriginalGivenInputProfile_phase_le D j ell nu
  have hfin : paperAtlasWeighted 0 j ell f O S ≠ ⊤ := ne_top_of_le_ne_top hfinite hle
  have hbound : (paperAtlasWeighted 0 j ell f O S).toReal ≤ budget :=
    (ENNReal.toReal_mono hfinite hle).trans hbudget
  have he := actual_paperAtlasWeighted_open_restrict 0 j ell f O U S hO hU
    (fun _ => inter_subset_left) hSU
  rw [he] at hfin hbound
  have hj := paperAtlasWeighted_shifted_joint_jet_le 0 j ell hell f U S hU hSU hf hfin i hk
    (le_refl 0) hz
  simp only [Nat.add_zero] at hj
  have hcoef : ell^k*‖iteratedFDeriv ℝ k (f i) (a z)‖ ≤ coordinateDimensionFactor (n+d) j*budget :=
    hj.trans (mul_le_mul_of_nonneg_left hbound (coordinateDimensionFactor_nonneg _ _))
  have hDf : fderiv ℝ (actualOriginalJointPhase D nu i) = actualScalarCovectorAssembly (n+d) ∘ f i := by
    funext y
    exact (actualScalarCovectorAssembly_exact (n+d) (fderiv ℝ (actualOriginalJointPhase D nu i) y)).symm
  have hp := slow_linear_jet_bound (actualScalarCovectorAssembly (n+d)) (U i) (hU i) (f i) (hf i)
    k ell (coordinateDimensionFactor (n+d) j*budget) hell.le (a z) (hSU i hz) hcoef
  rw [← hDf,norm_iteratedFDeriv_fderiv] at hp
  have hpre := norm_iteratedFDeriv_comp_equiv_le a (actualOriginalJointPhase D nu i) (k+1) z
  have hbudget0 : 0 ≤ budget := ENNReal.toReal_nonneg.trans hbudget
  calc
    _ ≤ ell^k*(‖iteratedFDeriv ℝ (k+1) (actualOriginalJointPhase D nu i) (a z)‖*
        linearModelFactor a (k+1)) := mul_le_mul_of_nonneg_left hpre (pow_nonneg hell.le k)
    _ = linearModelFactor a (k+1)*(ell^k*‖iteratedFDeriv ℝ (k+1) (actualOriginalJointPhase D nu i) (a z)‖) := by ring
    _ ≤ linearModelFactor a (j+1)*(‖actualScalarCovectorAssembly (n+d)‖*
        (coordinateDimensionFactor (n+d) j*budget)) :=
      mul_le_mul (linearModelFactor_mono a (by omega)) hp (by positivity) (linearModelFactor_nonneg _ _)
    _ = _ := by dsimp only [actualOriginalTotalPhaseJetCost,a]; ring

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_original_given_phase_positive_jets
