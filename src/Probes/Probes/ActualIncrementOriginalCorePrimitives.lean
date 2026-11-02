import Probes.ActualIncrementOriginalOpenCore

/-! Literal original cutoff and given-normal entries of the frozen Core.
The true parameter-open/primary differentiation region is retained and
quantitative bounds are required only on the unchanged original samples. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff ENNReal Topology BigOperators
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

private local instance primitiveCoreProductCharted : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
private local instance primitiveCoreProductManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,Es)) (n := ∞) P M

def actualOriginalPrimaryCoordinateOpen
    (Data : IncrementsOriginalNativeData n d N M P) (nu : Fin Data.primaryCount)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) : Set (Fin (n+d) → ℝ) :=
  incrementsOriginalPrimaryDifferentiation Data nu i ∩
    (incrementsOriginalJointPoint Data.atlas Data.parameterChart i) ⁻¹' incrementsOriginalParameterRegion Data

def actualOriginalPrimaryNativeOpen
    (Data : IncrementsOriginalNativeData n d N M P) (nu : Fin Data.primaryCount)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) : Set X :=
  (parameterTensorModelEquiv n d) ⁻¹' actualOriginalPrimaryCoordinateOpen Data nu i

theorem actualOriginalPrimaryCoordinateOpen_isOpen
    (Data : IncrementsOriginalNativeData n d N M P) (hd : IncrementsOriginalDomainConditions Data)
    (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount) :
    IsOpen (actualOriginalPrimaryCoordinateOpen Data nu i) := by
  have h := (actual_original_jointPoint_continuousOn Data i).isOpen_inter_preimage
    (parameterRound2_originalDifferentiation_open Data.atlas Data.parameterChart i)
    ((hd.primary_open nu).inter (hd.parameter_open.prod isOpen_univ))
  simpa only [actualOriginalPrimaryCoordinateOpen,incrementsOriginalPrimaryDifferentiation,
    incrementsOriginalParameterRegion,preimage_inter,inter_assoc] using h

theorem actualOriginalPrimaryNativeOpen_isOpen
    (Data : IncrementsOriginalNativeData n d N M P) (hd : IncrementsOriginalDomainConditions Data)
    (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount) :
    IsOpen (actualOriginalPrimaryNativeOpen Data nu i) :=
  (actualOriginalPrimaryCoordinateOpen_isOpen Data hd nu i).preimage
    (parameterTensorModelEquiv n d).continuous

theorem actualOriginalPrimaryCoordinateOpen_samples
    (Data : IncrementsOriginalNativeData n d N M P) (hd : IncrementsOriginalDomainConditions Data)
    (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount) :
    incrementsOriginalPrimaryEvaluation Data nu i ⊆ actualOriginalPrimaryCoordinateOpen Data nu i := by
  intro z hz
  exact ⟨⟨hz.1.1,hz.2⟩,hd.parameter_subset hz.1.2.2.2,mem_univ _⟩

theorem actual_original_primary_field_coordinate_smooth
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {q : ℕ}
    (Data : IncrementsOriginalNativeData n d N M P) (hd : IncrementsOriginalDomainConditions Data)
    (nu : Fin Data.primaryCount) (f : P × M → Y)
    (hf : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓘(ℝ,Es)) 𝓘(ℝ,Y) ∞ f
      (Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data))
    (cy : Y →L[ℝ] (Fin q → ℝ))
    (i : Fin Data.atlas.count × Fin Data.parameterCount) :
    ContDiffOn ℝ ∞ (fun z => cy (f (incrementsOriginalJointPoint Data.atlas Data.parameterChart i z)))
      (actualOriginalPrimaryCoordinateOpen Data nu i) := by
  let e := (Data.parameterChart i.2).prod (Data.atlas.chart i.1)
  let a := parameterTensorModelEquiv n d
  let R := Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.mem_maximalAtlas_prod (hd.parameter_charts_smooth i.2)
      (hd.atlas_smooth.chart_mem i.1)
  have hF : ContMDiffOn 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Y) ∞ f R := by
    rw [modelWithCornersSelf_prod]
    exact hf
  have hup := cy.contDiff.contMDiff.comp_contMDiffOn hF
  letI : ChartedSpace (Ep × Es) (Ep × Es) := chartedSpaceSelf (Ep × Es)
  have hi : ContMDiffOn 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ep × Es) ∞ e.symm e.target :=
    contMDiffOn_symm_of_mem_maximalAtlas he
  have hnative : ContDiffOn ℝ ∞ ((cy ∘ f) ∘ e.symm) (e.target ∩ e.symm ⁻¹' R) :=
    (hup.comp (hi.mono inter_subset_left) (fun _ hx => hx.2)).contDiffOn
  have hmap : MapsTo a.symm (actualOriginalPrimaryCoordinateOpen Data nu i)
      (e.target ∩ e.symm ⁻¹' R) := by
    intro z hz
    exact ⟨⟨hz.1.1.2,hz.1.1.1⟩,hz.1.2,hz.2⟩
  exact hnative.comp a.symm.contDiff.contDiffOn hmap

theorem actual_original_core_cutoff_le
    (Data : IncrementsOriginalNativeData n d N M P) (nu : Fin Data.primaryCount)
    (j : ℕ) (ell : ℝ) :
    paperAtlasWeighted 0 j ell (incrementsOriginalScalarCoordinates Data (Data.cutoff nu))
      (incrementsOriginalPrimaryDifferentiation Data nu) (incrementsOriginalPrimaryEvaluation Data nu) ≤
        incrementsOriginalCoreInputProfile Data j ell := by
  exact (le_max_left _ _).trans ((le_iSup (fun v : Fin Data.primaryCount =>
    max (paperAtlasWeighted 0 j ell (incrementsOriginalScalarCoordinates Data (Data.cutoff v))
      (incrementsOriginalPrimaryDifferentiation Data v) (incrementsOriginalPrimaryEvaluation Data v))
      (max (paperAtlasWeighted 0 j ell
        (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (Data.freeNormal v))
          (incrementsOriginalPrimaryDifferentiation Data v) (incrementsOriginalPrimaryEvaluation Data v))
        (paperAtlasWeighted 0 j ell (incrementsOriginalPhaseCovectorCoordinates Data v)
          (incrementsOriginalPrimaryDifferentiation Data v) (incrementsOriginalPrimaryEvaluation Data v)))) nu).trans
    ((le_max_right _ _).trans (le_max_right _ _)))

theorem actual_original_core_normal_le
    (Data : IncrementsOriginalNativeData n d N M P) (nu : Fin Data.primaryCount)
    (j : ℕ) (ell : ℝ) :
    paperAtlasWeighted 0 j ell (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (Data.freeNormal nu))
      (incrementsOriginalPrimaryDifferentiation Data nu) (incrementsOriginalPrimaryEvaluation Data nu) ≤
        incrementsOriginalCoreInputProfile Data j ell := by
  exact ((le_max_left _ _).trans (le_max_right _ _)).trans
    ((le_iSup (fun v : Fin Data.primaryCount =>
      max (paperAtlasWeighted 0 j ell (incrementsOriginalScalarCoordinates Data (Data.cutoff v))
        (incrementsOriginalPrimaryDifferentiation Data v) (incrementsOriginalPrimaryEvaluation Data v))
        (max (paperAtlasWeighted 0 j ell
          (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (Data.freeNormal v))
            (incrementsOriginalPrimaryDifferentiation Data v) (incrementsOriginalPrimaryEvaluation Data v))
          (paperAtlasWeighted 0 j ell (incrementsOriginalPhaseCovectorCoordinates Data v)
            (incrementsOriginalPrimaryDifferentiation Data v) (incrementsOriginalPrimaryEvaluation Data v)))) nu).trans
      ((le_max_right _ _).trans (le_max_right _ _)))

theorem actual_original_primary_core_field_jets
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {q : ℕ}
    (Data : IncrementsOriginalNativeData n d N M P) (hd : IncrementsOriginalDomainConditions Data)
    (nu : Fin Data.primaryCount) (cy : (Fin q → ℝ) ≃L[ℝ] Y)
    (f : (Fin Data.atlas.count × Fin Data.parameterCount) → (Fin (n+d) → ℝ) → Fin q → ℝ)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (actualOriginalPrimaryCoordinateOpen Data nu i))
    (j : ℕ) (ell : ℝ) (hell : 0 < ell)
    (hentry : paperAtlasWeighted 0 j ell f (incrementsOriginalPrimaryDifferentiation Data nu)
      (incrementsOriginalPrimaryEvaluation Data nu) ≤ incrementsOriginalCoreInputProfile Data j ell)
    (hfinite : incrementsOriginalCoreInputProfile Data j ell ≠ ⊤)
    (budget : ℝ) (hbudget : (incrementsOriginalCoreInputProfile Data j ell).toReal ≤ budget)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) :
    ContDiffOn ℝ ∞ (cy ∘ f i ∘ parameterTensorModelEquiv n d) (actualOriginalPrimaryNativeOpen Data nu i) ∧
      ∀ k ≤ j, ∀ z, parameterTensorModelEquiv n d z ∈ incrementsOriginalPrimaryEvaluation Data nu i →
        ell^k*‖iteratedFDeriv ℝ k (cy ∘ f i ∘ parameterTensorModelEquiv n d) z‖ ≤
          (‖cy.toContinuousLinearMap‖*linearModelFactor (parameterTensorModelEquiv n d) j*
            coordinateDimensionFactor (n+d) j)*budget := by
  let O := incrementsOriginalPrimaryDifferentiation Data nu
  let U := actualOriginalPrimaryCoordinateOpen Data nu
  let S := incrementsOriginalPrimaryEvaluation Data nu
  have hO : ∀ i, IsOpen (O i) := actual_original_primaryDifferentiation_open Data hd.primary_open nu
  have hU : ∀ i, IsOpen (U i) := actualOriginalPrimaryCoordinateOpen_isOpen Data hd nu
  have hSU : ∀ i, S i ⊆ U i := actualOriginalPrimaryCoordinateOpen_samples Data hd nu
  have he := actual_paperAtlasWeighted_open_restrict 0 j ell f O U S hO hU
    (fun _ => inter_subset_left) hSU
  have hfin : paperAtlasWeighted 0 j ell f U S ≠ ⊤ := he ▸ ne_top_of_le_ne_top hfinite hentry
  refine ⟨cy.contDiff.comp_contDiffOn ((hf i).comp
    (parameterTensorModelEquiv n d).contDiff.contDiffOn (fun _ hz => hz)),?_⟩
  intro k hk z hz
  have hh := paperAtlasWeighted_native_shifted_joint_jet_le (parameterTensorModelEquiv n d) cy
    0 j ell hell f U S hU hSU hf hfin i hk (le_refl 0) hz
  simp only [Nat.add_zero] at hh
  rw [← he] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    ((ENNReal.toReal_mono hfinite hentry).trans hbudget)
    (mul_nonneg (mul_nonneg (norm_nonneg _) (linearModelFactor_nonneg _ _))
      (coordinateDimensionFactor_nonneg _ _)))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_primary_field_coordinate_smooth
#print axioms GlobalEmbedding.Continuation.actual_original_core_cutoff_le
#print axioms GlobalEmbedding.Continuation.actual_original_core_normal_le
#print axioms GlobalEmbedding.Continuation.actual_original_primary_core_field_jets
