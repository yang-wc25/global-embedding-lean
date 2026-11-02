import Smoothing.ParameterRound2CoreSampling
import GlobalEmbedding.Paper.IncrementsOriginalQualitativeAdmissibility

/-!
# Original compact-manifold input regularity on the actual smoothing charts

This module uses the unchanged IncrementsOriginalSmoothInputs on the full
parameter manifold, `parameterOpen = univ`. The actual native F then is
jointly smooth, and its original coordinate representative is smooth on the
real original differentiation domain. The actual native H coordinate field
has the same property. No extra smoothness of a desired output is assumed.
-/

open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set Manifold IsManifold
open scoped ContDiff
namespace GlobalEmbedding.Continuation
noncomputable section

variable {n d N pcount : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]

local instance parameterRound2OriginalInputsChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance parameterRound2OriginalInputsIsManifold : IsManifold
    𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) P M

local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ey" => EuclideanSpace ℝ (Fin N)

/-- Actual native smoothness implies original full-joint map-coordinate
smoothness even when the finite parameter chart family is not a cover. -/
theorem parameterRound2_localMapCoordinates_contDiffOn
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ, Ep) ∞ P)
    (u : P × M → Ey) (hu : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ u)
    (i : Fin A.count × Fin pcount) :
    ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B.chart u i)
      (incrementsOriginalDifferentiation A B.chart i) := by
  let C := parameterLocalProductFamily A B
  let c := parameterTensorModelEquiv n d
  let cy := EuclideanSpace.equiv (Fin N) ℝ
  have hupi : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Fin N → ℝ) ∞ (cy ∘ u) :=
    cy.contDiff.contMDiff.comp hu
  have hnative : ∀ k, ContDiffOn ℝ ∞ ((cy ∘ u) ∘ (C.chart k).symm) (C.chart k).target := by
    intro k
    letI : ChartedSpace (Ep × Es) (Ep × Es) := chartedSpaceSelf (Ep × Es)
    have hk : ContMDiffOn 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ep × Es) ∞ (C.chart k).symm (C.chart k).target :=
      contMDiffOn_symm_of_mem_maximalAtlas (parameterLocalProductFamily_chart_mem A B hA hB k)
    have hcomp : ContMDiffOn 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Fin N → ℝ) ∞
        ((cy ∘ u) ∘ (C.chart k).symm) (C.chart k).target := hupi.comp_contMDiffOn hk
    exact hcomp.contDiffOn
  have h := modelCoordinateFamily_contDiffOn c hnative i
  change ContDiffOn ℝ ∞ (parameterLocalMapModelCoordinates C c (cy ∘ u) i)
    (tensorLocalModelTargets C c i) at h
  rw [parameterLocalMapCoordinates_eq_original] at h
  change ContDiffOn ℝ ∞ _ ((parameterTensorModelEquiv n d).symm ⁻¹'
    ((parameterLocalProductFamily A B).chart i).target) at h
  rw [parameterLocalProduct_targets A B i] at h
  exact h

/-- Full parameter-manifold original inputs supply the actual map and tensor
regularity needed by the SAME joint smoothing operator. -/
theorem parameterRound2_original_full_parameter_inputs
    (D : IncrementsOriginalNativeData n d N M P)
    (B : TensorBufferedChartFamily (Fin D.parameterCount) P Ep)
    (hchart : B.chart = D.parameterChart)
    (hA : IsSmoothBufferedAtlas D.atlas)
    (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ, Ep) ∞ P)
    (hs : IncrementsOriginalSmoothInputs D) (hopen : D.parameterOpen = univ) :
    ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ D.F ∧
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates D.atlas B.chart D.F i)
      (incrementsOriginalDifferentiation D.atlas B.chart i)) ∧
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates D.atlas B.chart D.H i)
      (incrementsOriginalDifferentiation D.atlas B.chart i)) := by
  have hF : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ D.F := by
    have h := hs.F_joint
    rw [← modelWithCornersSelf_prod] at h
    simpa only [incrementsOriginalParameterRegion, hopen, Set.univ_prod_univ,
      contMDiffOn_univ] using h
  refine ⟨hF, parameterRound2_localMapCoordinates_contDiffOn D.atlas B hA hB D.F hF, ?_⟩
  intro i
  have h := hs.H_coordinates i
  simpa only [hchart, incrementsOriginalParameterRegion, hopen, Set.univ_prod_univ,
    Set.preimage_univ, Set.inter_univ] using h

/-- Direct chart calculation for the actual original map coordinates, with
the original source-first joint ABI. The parameter chart family is arbitrary
and need not be equipped with sampling buffers or a cover proof. -/
theorem parameterRound2_originalMapCoordinates_contDiffOn
    (A : BufferedAtlas M Es) (B : Fin pcount → OpenPartialHomeomorph P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B i ∈ maximalAtlas 𝓘(ℝ, Ep) ∞ P)
    (u : P × M → Ey) (hu : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ u)
    (i : Fin A.count × Fin pcount) :
    ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B u i)
      (incrementsOriginalDifferentiation A B i) := by
  let e := (B i.2).prod (A.chart i.1)
  let a := parameterTensorModelEquiv n d
  let cy := EuclideanSpace.equiv (Fin N) ℝ
  have he : e ∈ maximalAtlas 𝓘(ℝ, Ep × Es) ∞ (P × M) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.mem_maximalAtlas_prod (hB i.2) (hA.chart_mem i.1)
  have hup : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Fin N → ℝ) ∞ (cy ∘ u) :=
    cy.contDiff.contMDiff.comp hu
  have hnative : ContDiffOn ℝ ∞ ((cy ∘ u) ∘ e.symm) e.target := by
    letI : ChartedSpace (Ep × Es) (Ep × Es) := chartedSpaceSelf (Ep × Es)
    have hi : ContMDiffOn 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ep × Es) ∞ e.symm e.target :=
      contMDiffOn_symm_of_mem_maximalAtlas he
    have hcomp : ContMDiffOn 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Fin N → ℝ) ∞
        ((cy ∘ u) ∘ e.symm) e.target := hup.comp_contMDiffOn hi
    exact hcomp.contDiffOn
  have hmap : MapsTo a.symm (incrementsOriginalDifferentiation A B i) e.target := by
    intro y hy
    change incrementsOriginalParameterPoint y ∈ (B i.2).target ∧
      incrementsOriginalSourcePoint y ∈ (A.chart i.1).target
    exact ⟨hy.2, hy.1⟩
  exact hnative.comp a.symm.contDiff.contDiffOn hmap

/-- All genuine regularity obligations for the original full-parameter Core
come directly from its unchanged domain and smooth-input predicates. -/
theorem parameterRound2_original_full_parameter_coordinates
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D)
    (hs : IncrementsOriginalSmoothInputs D) (hopen : D.parameterOpen = univ) :
    ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ D.F ∧
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates D.atlas D.parameterChart D.F i)
      (incrementsOriginalDifferentiation D.atlas D.parameterChart i)) ∧
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates D.atlas D.parameterChart D.H i)
      (incrementsOriginalDifferentiation D.atlas D.parameterChart i)) := by
  have hF : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ D.F := by
    have h := hs.F_joint
    rw [← modelWithCornersSelf_prod] at h
    simpa only [incrementsOriginalParameterRegion, hopen, Set.univ_prod_univ,
      contMDiffOn_univ] using h
  refine ⟨hF,
    parameterRound2_originalMapCoordinates_contDiffOn D.atlas D.parameterChart
      hd.atlas_smooth hd.parameter_charts_smooth D.F hF, ?_⟩
  intro i
  simpa only [incrementsOriginalParameterRegion, hopen, Set.univ_prod_univ,
    Set.preimage_univ, Set.inter_univ] using hs.H_coordinates i

#print axioms parameterRound2_original_full_parameter_inputs
#print axioms parameterRound2_originalMapCoordinates_contDiffOn
#print axioms parameterRound2_original_full_parameter_coordinates
end
end GlobalEmbedding.Continuation
