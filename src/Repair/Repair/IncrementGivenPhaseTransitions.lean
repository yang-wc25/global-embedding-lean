import Repair.IncrementGivenPhaseExtraction
import Repair.EntranceOriginalObserverJets

/-! Every original joint transition differential is generated from the
 actual source and parameter transitions. The j-th derivative reads only
 their (j+1)-st positive jets, in the original observation domains. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

def incrementGivenTransitionPositiveProfile (n d : ℕ) (Parameter Spatial : ℕ → ℝ) (j : ℕ) : ℝ :=
  ‖(parameterTensorModelEquiv n d).toContinuousLinearMap‖*max (Parameter j) (Spatial j)*
    linearModelFactor (parameterTensorModelEquiv n d).symm j

def incrementGivenTransitionProfile (n d : ℕ) (Parameter Spatial : ℕ → ℝ) (j : ℕ) : ℝ :=
  ‖incrementGivenTransitionExtraction (n+d)‖*incrementGivenTransitionPositiveProfile n d Parameter Spatial (j+1)

theorem incrementGivenTransitionProfile_nonneg (n d : ℕ) (Parameter Spatial : ℕ → ℝ)
    (hParameter : ∀ j, 0 ≤ Parameter j) (hSpatial : ∀ j, 0 ≤ Spatial j) (j : ℕ) :
    0 ≤ incrementGivenTransitionProfile n d Parameter Spatial j :=
  mul_nonneg (norm_nonneg (incrementGivenTransitionExtraction (n+d)))
    (mul_nonneg (mul_nonneg (norm_nonneg _) ((hParameter _).trans (le_max_left _ _)))
      (linearModelFactor_nonneg _ _))

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "Y" => Fin (m+1+d) → ℝ

theorem increment_given_actual_native_transition_jets
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (Parameter Spatial : ℕ → ℝ) (transition : RepairOriginalTransitionBudgets Data Parameter Spatial)
    (ik : (Fin Data.atlas.count × Fin Data.parameterCount) × (Fin Data.atlas.count × Fin Data.parameterCount))
    (y : Y) (hy : y ∈ actualOriginalGivenTransitionSample Data ik)
    (j : ℕ) (hj : 1 ≤ j) :
    let native : X → X := fun z =>
      (Data.parameterChart ik.2.2 ((Data.parameterChart ik.1.2).symm z.1),
        Data.atlas.chart ik.2.1 ((Data.atlas.chart ik.1.1).symm z.2))
    ContDiffAt ℝ ∞ native ((parameterTensorModelEquiv (m+1) d).symm y) ∧
      ‖iteratedFDeriv ℝ j native ((parameterTensorModelEquiv (m+1) d).symm y)‖ ≤ max (Parameter j) (Spatial j) := by
  intro actualNative
  let a := parameterTensorModelEquiv (m+1) d
  let z := a.symm y
  let C := (Data.parameterChart ik.1.2).symm.trans (Data.parameterChart ik.2.2)
  let Q := C.prod (OpenPartialHomeomorph.refl D)
  let S := repairReferenceHostTransition («Ep» := Ep) (Data.atlas.chart ik.1.1) (Data.atlas.chart ik.2.1)
  have hzQ : z ∈ Q.source := ⟨⟨hy.1.1.2,hy.2.2.1⟩,mem_univ _⟩
  have hzS : z ∈ S.source := ⟨mem_univ _,hy.1.1.1,hy.2.2.2⟩
  have hC : ContDiffOn ℝ ∞ C C.source :=
    (round3Parameter_partial_trans_smooth (Data.parameterChart ik.1.2).symm (Data.parameterChart ik.2.2)
      (contMDiffOn_symm_of_mem_maximalAtlas (hd.parameter_charts_smooth ik.1.2))
      (contMDiffOn_of_mem_maximalAtlas (hd.parameter_charts_smooth ik.2.2))).contDiffOn
  have hQ : ContDiffAt ℝ ∞ Q z :=
    (hC.prodMap contDiff_id.contDiffOn).contDiffAt (Q.open_source.mem_nhds hzQ)
  have hS : ContDiffAt ℝ ∞ S z :=
    (repair_reference_host_transition_smooth («Ep» := Ep) (Data.atlas.chart ik.1.1) (Data.atlas.chart ik.2.1)
      (hd.atlas_smooth.chart_mem ik.1.1) (hd.atlas_smooth.chart_mem ik.2.1)).1.contDiffAt (S.open_source.mem_nhds hzS)
  have hQb := transition.parameter ik.1.2 ik.2.2 j hj z hy.1.2.2.1 hzQ
  have hSb := transition.spatial ik.1.1 ik.2.1 j hj z hy.1.2.1 hzS
  let f : X → Ep := fun w => (Q w).1
  let g : X → D := fun w => (S w).2
  have hf : ContDiffAt ℝ ∞ f z := hQ.fst
  have hg : ContDiffAt ℝ ∞ g z := hS.snd
  have hfb : ‖iteratedFDeriv ℝ j f z‖ ≤ Parameter j := by
    have hh := (ContinuousLinearMap.fst ℝ Ep D).norm_iteratedFDeriv_comp_left hQ (n := j) (by simp)
    exact hh.trans ((mul_le_of_le_one_left (norm_nonneg _) (ContinuousLinearMap.norm_fst_le ℝ Ep D)).trans hQb)
  have hgb : ‖iteratedFDeriv ℝ j g z‖ ≤ Spatial j := by
    have hh := (ContinuousLinearMap.snd ℝ Ep D).norm_iteratedFDeriv_comp_left hS (n := j) (by simp)
    exact hh.trans ((mul_le_of_le_one_left (norm_nonneg _) (ContinuousLinearMap.norm_snd_le ℝ Ep D)).trans hSb)
  let native : X → X := fun w => (f w,g w)
  have hn : ContDiffAt ℝ ∞ native z := hf.prodMk hg
  have hnb : ‖iteratedFDeriv ℝ j native z‖ ≤ max (Parameter j) (Spatial j) := by
    rw [iteratedFDeriv_prodMk (hf.of_le (by simp)) (hg.of_le (by simp)) le_rfl,
      ContinuousMultilinearMap.opNorm_prod]
    exact max_le_max hfb hgb
  exact ⟨hn,hnb⟩

theorem increment_given_actual_transition_positive_jets
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (Parameter Spatial : ℕ → ℝ) (transition : RepairOriginalTransitionBudgets Data Parameter Spatial)
    (ik : (Fin Data.atlas.count × Fin Data.parameterCount) × (Fin Data.atlas.count × Fin Data.parameterCount))
    (y : Y) (hy : y ∈ actualOriginalGivenTransitionSample Data ik)
    (j : ℕ) (hj : 1 ≤ j) :
    ‖iteratedFDeriv ℝ j (actualOriginalGivenTransition Data ik.1 ik.2) y‖ ≤
      incrementGivenTransitionPositiveProfile (m+1) d Parameter Spatial j := by
  let a := parameterTensorModelEquiv (m+1) d
  let z := a.symm y
  let native : X → X := fun z =>
    (Data.parameterChart ik.2.2 ((Data.parameterChart ik.1.2).symm z.1),
      Data.atlas.chart ik.2.1 ((Data.atlas.chart ik.1.1).symm z.2))
  obtain ⟨hn,hnb⟩ := increment_given_actual_native_transition_jets Data hd Parameter Spatial transition ik y hy j hj
  have hout := a.toContinuousLinearMap.norm_iteratedFDeriv_comp_left hn (n := j) (by simp)
  have houtb : ‖iteratedFDeriv ℝ j (a ∘ native) z‖ ≤
      ‖a.toContinuousLinearMap‖*max (Parameter j) (Spatial j) :=
    hout.trans (mul_le_mul_of_nonneg_left hnb (norm_nonneg _))
  have he : actualOriginalGivenTransition Data ik.1 ik.2 = (a ∘ native) ∘ a.symm := by
    funext u
    rfl
  rw [he]
  exact (norm_iteratedFDeriv_comp_equiv_le a.symm (a ∘ native) j y).trans
    (mul_le_mul_of_nonneg_right houtb (linearModelFactor_nonneg _ _))

theorem increment_given_actual_transition_differential_jets
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (Parameter Spatial : ℕ → ℝ) (transition : RepairOriginalTransitionBudgets Data Parameter Spatial)
    (ik : (Fin Data.atlas.count × Fin Data.parameterCount) × (Fin Data.atlas.count × Fin Data.parameterCount))
    (y : Y) (hy : y ∈ actualOriginalGivenTransitionSample Data ik) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (actualOriginalGivenTransitionDifferentialCoordinates Data ik) y‖ ≤
      incrementGivenTransitionProfile (m+1) d Parameter Spatial j := by
  have hf := (actualOriginalGivenTransition_contDiffOn Data hd ik).contDiffAt
    ((actualOriginalGivenTransitionDomain_open Data ik).mem_nhds hy.2)
  exact increment_given_derivative_extraction_jets (incrementGivenTransitionExtraction (m+1+d))
    (actualOriginalGivenTransition Data ik.1 ik.2) y hf j _
    (increment_given_actual_transition_positive_jets Data hd Parameter Spatial transition ik y hy (j+1) (by omega))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.increment_given_actual_transition_positive_jets
#print axioms GlobalEmbedding.Continuation.increment_given_actual_transition_differential_jets

#print axioms GlobalEmbedding.Continuation.increment_given_actual_native_transition_jets
