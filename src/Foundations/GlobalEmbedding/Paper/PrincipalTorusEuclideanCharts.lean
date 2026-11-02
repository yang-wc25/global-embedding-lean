import GlobalEmbedding.Paper.PrincipalTorusBundle
import GlobalEmbedding.Paper.PrincipalTorusLiftDerivatives
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Genuine Euclidean-base local principal torus charts

Source: `main.tex`, `lem:balanced`, line418. Compose actual bundle charts with actual
base charts and a real continuous linear equivalence of their finite-dimensional model.
Only the local base coordinate domain is Euclidean; the base manifold is preserved.
-/

noncomputable section
open Set WithLp IsManifold
open scoped Manifold ContDiff
namespace GlobalEmbedding.Paper
local instance principalTorusEuclideanChartsTorusAtlas (a : ℕ) :
    ChartedSpace (EuclideanSpace ℝ (Fin a)) (PeriodOneTorus a) :=
  periodicFlatTorusChartedSpace a
local instance principalTorusEuclideanChartsTorusManifold (a : ℕ) :
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin a)) ∞ (PeriodOneTorus a) :=
  periodic_flat_torus_isManifold a ∞

variable {EB B : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace B] [ChartedSpace EB B]

/-- The actual finite-dimensional base model has genuine Euclidean coordinates. -/
def principalTorusEuclideanModelEquiv [FiniteDimensional ℝ EB] :
    EB ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ EB)) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- An actual base chart, transported by a genuine linear model equivalence. -/
def principalTorusBaseCoordinateChart (L : EB ≃L[ℝ] F) (b : B) :
    OpenPartialHomeomorph B F :=
  (chartAt EB b).trans L.toHomeomorph.toOpenPartialHomeomorph

/-- Identity model transport recovers exactly the original actual base chart. -/
theorem principalTorusBaseCoordinateChart_refl (b : B) :
    principalTorusBaseCoordinateChart (ContinuousLinearEquiv.refl ℝ EB) b = chartAt EB b := by
  change (chartAt EB b).trans (OpenPartialHomeomorph.refl EB) = chartAt EB b
  exact (chartAt EB b).trans_refl

variable [IsManifold 𝓘(ℝ, EB) ∞ B]

omit [IsManifold 𝓘(ℝ, EB) ∞ B] in
theorem principalTorusBaseCoordinateChart_mem_source (L : EB ≃L[ℝ] F) (b : B) :
    b ∈ (principalTorusBaseCoordinateChart L b).source := by
  exact ⟨mem_chart_source EB b, mem_univ _⟩

theorem contMDiffOn_principalTorusBaseCoordinateChart (L : EB ≃L[ℝ] F) (b : B) :
    ContMDiffOn 𝓘(ℝ, EB) 𝓘(ℝ, F) ∞
      (principalTorusBaseCoordinateChart L b) (principalTorusBaseCoordinateChart L b).source := by
  exact L.toContinuousLinearMap.contMDiff.comp_contMDiffOn
    (contMDiffOn_chart.mono (fun _ hx ↦ hx.1))

theorem contMDiffOn_principalTorusBaseCoordinateChart_symm (L : EB ≃L[ℝ] F) (b : B) :
    ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, EB) ∞
      (principalTorusBaseCoordinateChart L b).symm
      (principalTorusBaseCoordinateChart L b).target := by
  exact contMDiffOn_chart_symm.comp L.symm.toContinuousLinearMap.contMDiff.contMDiffOn
    (fun _ hx ↦ hx.2)

variable {E H M ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M]
namespace PrincipalTorusBundle
variable {a : ℕ} {I : ModelWithCorners ℝ E H} {π : M → B}
  [IsManifold I ∞ M] [AddAction (PeriodOneTorus a) M]
  (S : PrincipalTorusBundle (ι := ι) a I 𝓘(ℝ, EB) π)
include S

/-- The genuine bundle chart refined by a local Euclidean coordinate chart on the base. -/
def coordinateBundleChart (L : EB ≃L[ℝ] F) (i : ι) (b : B) :
    OpenPartialHomeomorph M (F × PeriodOneTorus a) :=
  (S.trivialization i).toOpenPartialHomeomorph.trans
    ((principalTorusBaseCoordinateChart L b).prod (OpenPartialHomeomorph.refl (PeriodOneTorus a)))

/-- The actual open Euclidean parameter domain of the refined local full-fiber chart. -/
def coordinateBundleBaseSet (L : EB ≃L[ℝ] F) (i : ι) (b : B) :
    Set (F) :=
  (principalTorusBaseCoordinateChart L b).target ∩
    (principalTorusBaseCoordinateChart L b).symm ⁻¹' (S.trivialization i).baseSet

theorem isOpen_coordinateBundleBaseSet
    (L : EB ≃L[ℝ] F) (i : ι) (b : B) :
    IsOpen (S.coordinateBundleBaseSet L i b) :=
  (principalTorusBaseCoordinateChart L b).isOpen_inter_preimage_symm
    (S.trivialization i).open_baseSet

theorem coordinateBundleChart_target
    (L : EB ≃L[ℝ] F) (i : ι) (b : B) :
    (S.coordinateBundleChart L i b).target = S.coordinateBundleBaseSet L i b ×ˢ univ := by
  ext z
  simp only [coordinateBundleChart, coordinateBundleBaseSet,
    OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.prod_target,
    OpenPartialHomeomorph.refl_target, OpenPartialHomeomorph.prod_symm_apply,
    (S.trivialization i).target_eq,
    mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true]

/-- Source membership is exactly the two actual overlapping base neighborhoods. -/
theorem coordinateBundleChart_mem_source_iff
    (L : EB ≃L[ℝ] F) (i : ι) (b : B) (x : M) :
    x ∈ (S.coordinateBundleChart L i b).source ↔
      x ∈ (S.trivialization i).source ∧ π x ∈ (principalTorusBaseCoordinateChart L b).source := by
  change (x ∈ (S.trivialization i).source ∧
    (S.trivialization i x).1 ∈ (principalTorusBaseCoordinateChart L b).source ∧ True) ↔ _
  constructor
  · intro hx
    exact ⟨hx.1, ((S.trivialization i).coe_fst hx.1) ▸ hx.2.1⟩
  · intro hx
    exact ⟨hx.1, ((S.trivialization i).coe_fst hx.1).symm ▸ hx.2, trivial⟩

/-- These true refined local charts cover the original total manifold. -/
theorem coordinateBundleChart_cover
    (L : EB ≃L[ℝ] F) (x : M) :
    ∃ k : ι × B, x ∈ (S.coordinateBundleChart L k.1 k.2).source := by
  obtain ⟨i, hi⟩ := S.exists_mem_source x
  exact ⟨(i, π x), (S.coordinateBundleChart_mem_source_iff L i (π x) x).mpr
    ⟨hi, principalTorusBaseCoordinateChart_mem_source L (π x)⟩⟩

/-- The actual full local chart is genuinely manifold-smooth on its own source. -/
theorem contMDiffOn_coordinateBundleChart
    (L : EB ≃L[ℝ] F) (i : ι) (b : B) :
    ContMDiffOn I (𝓘(ℝ, F).prod
      𝓘(ℝ, EuclideanSpace ℝ (Fin a))) ∞
      (S.coordinateBundleChart L i b) (S.coordinateBundleChart L i b).source := by
  have hg : ContMDiffOn (𝓘(ℝ, EB).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin a)))
      (𝓘(ℝ, F).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin a))) ∞
      ((principalTorusBaseCoordinateChart L b).prod (OpenPartialHomeomorph.refl (PeriodOneTorus a)))
      ((principalTorusBaseCoordinateChart L b).prod (OpenPartialHomeomorph.refl (PeriodOneTorus a))).source :=
    (contMDiffOn_principalTorusBaseCoordinateChart L b).prodMap contMDiff_id.contMDiffOn
  exact hg.comp ((S.smooth_trivialization i).mono (fun _ hx ↦ hx.1)) (fun _ hx ↦ hx.2)

/-- The actual inverse local chart is genuinely manifold-smooth on its true full-fiber target. -/
theorem contMDiffOn_coordinateBundleChart_symm
    (L : EB ≃L[ℝ] F) (i : ι) (b : B) :
    ContMDiffOn (𝓘(ℝ, F).prod
      𝓘(ℝ, EuclideanSpace ℝ (Fin a))) I ∞
      (S.coordinateBundleChart L i b).symm (S.coordinateBundleChart L i b).target := by
  have hg : ContMDiffOn
      (𝓘(ℝ, F).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin a)))
      (𝓘(ℝ, EB).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin a))) ∞
      ((principalTorusBaseCoordinateChart L b).prod (OpenPartialHomeomorph.refl (PeriodOneTorus a))).symm
      ((principalTorusBaseCoordinateChart L b).prod (OpenPartialHomeomorph.refl (PeriodOneTorus a))).target :=
    (contMDiffOn_principalTorusBaseCoordinateChart_symm L b).prodMap
      contMDiff_id.contMDiffOn
  exact (S.smooth_inverse i).comp (hg.mono (fun _ hx ↦ hx.1)) (fun _ hx ↦ hx.2)

/-- Refinement changes only the base coordinates; it retains the genuine torus coordinate. -/
theorem coordinateBundleChart_apply
    (L : EB ≃L[ℝ] F) (i : ι) (b : B) {x : M}
    (hx : x ∈ (S.trivialization i).source) :
    S.coordinateBundleChart L i b x =
      (principalTorusBaseCoordinateChart L b (π x), (S.trivialization i x).2) := by
  change ((principalTorusBaseCoordinateChart L b) (S.trivialization i x).1,
    (S.trivialization i x).2) = _
  rw [(S.trivialization i).coe_fst hx]

/-- The inverse refined chart is the same native fiber chart at its actual base point. -/
theorem coordinateBundleChart_symm_apply
    (L : EB ≃L[ℝ] F) (i : ι) (b : B)
    (p : F) (t : PeriodOneTorus a) :
    (S.coordinateBundleChart L i b).symm (p, t) =
      S.fiberChartPoint i ((principalTorusBaseCoordinateChart L b).symm p) t := rfl

/-- Literal pullback identity for every actual source datum, including linear-map coefficients. -/
theorem coordinateBundleChart_source_pullback {V : Type*} (f : M → V)
    (L : EB ≃L[ℝ] F) (i : ι) (b : B)
    (p : F) (y : EuclideanSpace ℝ (Fin a)) :
    f ((S.coordinateBundleChart L i b).symm
      (p, toLp 2 (fun j ↦ (y j : AddCircle (1 : ℝ))))) =
      f (S.fiberEuclideanLift i ((principalTorusBaseCoordinateChart L b).symm p) y) := rfl

/-- The actual joint Euclidean lift of the inverse local bundle chart is native C∞.
Its domain is exactly the genuine open Euclidean baseSet times the entire fiber lift. -/
theorem contMDiffOn_coordinateBundleChart_jointLift
    (L : EB ≃L[ℝ] F) (i : ι) (b : B) :
    ContMDiffOn (𝓘(ℝ, F).prod
      𝓘(ℝ, EuclideanSpace ℝ (Fin a))) I ∞
      (fun z : F × EuclideanSpace ℝ (Fin a) ↦
        (S.coordinateBundleChart L i b).symm
          (z.1, toLp 2 (fun j ↦ (z.2 j : AddCircle (1 : ℝ)))))
      (S.coordinateBundleBaseSet L i b ×ˢ univ) := by
  have hquot : ContMDiff
      (𝓘(ℝ, F).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin a)))
      (𝓘(ℝ, F).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin a))) ∞
      (fun z : F × EuclideanSpace ℝ (Fin a) ↦
        (z.1, toLp 2 (fun j ↦ (z.2 j : AddCircle (1 : ℝ))))) :=
    contMDiff_fst.prodMk ((periodic_flat_torus_projection_contMDiff a ∞).comp contMDiff_snd)
  exact (S.contMDiffOn_coordinateBundleChart_symm L i b).comp hquot.contMDiffOn
    (fun z hz ↦ by rw [S.coordinateBundleChart_target L i b]; exact ⟨hz.1, mem_univ _⟩)

/-- The exact native EB-valued chart requested for compact subordinate base refinement. -/
abbrev nativeBundleChart (i : ι) (b : B) : OpenPartialHomeomorph M (EB × PeriodOneTorus a) :=
  S.coordinateBundleChart (ContinuousLinearEquiv.refl ℝ EB) i b

/-- Its exact original native-base coordinate domain. -/
def nativeBundleBaseSet (i : ι) (b : B) : Set EB :=
  (chartAt EB b).target ∩ (chartAt EB b).symm ⁻¹' (S.trivialization i).baseSet

theorem nativeBundleChart_target (i : ι) (b : B) :
    (S.nativeBundleChart i b).target = S.nativeBundleBaseSet i b ×ˢ univ := by
  rw [S.coordinateBundleChart_target]
  simp only [coordinateBundleBaseSet, principalTorusBaseCoordinateChart_refl,
    nativeBundleBaseSet]

theorem nativeBundleChart_source (i : ι) (b : B) :
    (S.nativeBundleChart i b).source =
      (S.trivialization i).source ∩ π ⁻¹' (chartAt EB b).source := by
  ext x
  rw [S.coordinateBundleChart_mem_source_iff, principalTorusBaseCoordinateChart_refl]
  rfl

theorem nativeBundleChart_apply (i : ι) (b : B) {x : M}
    (hx : x ∈ (S.trivialization i).source) :
    S.nativeBundleChart i b x = ((chartAt EB b) (π x), (S.trivialization i x).2) := by
  simpa only [principalTorusBaseCoordinateChart_refl] using
    S.coordinateBundleChart_apply (ContinuousLinearEquiv.refl ℝ EB) i b hx

theorem nativeBundleChart_symm_apply (i : ι) (b : B) (p : EB) (t : PeriodOneTorus a) :
    (S.nativeBundleChart i b).symm (p, t) = S.fiberChartPoint i ((chartAt EB b).symm p) t := by
  simpa only [principalTorusBaseCoordinateChart_refl] using
    S.coordinateBundleChart_symm_apply (ContinuousLinearEquiv.refl ℝ EB) i b p t

theorem contMDiffOn_nativeBundleChart (i : ι) (b : B) :
    ContMDiffOn I (𝓘(ℝ, EB).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin a))) ∞
      (S.nativeBundleChart i b) (S.nativeBundleChart i b).source :=
  S.contMDiffOn_coordinateBundleChart (ContinuousLinearEquiv.refl ℝ EB) i b

theorem contMDiffOn_nativeBundleChart_symm (i : ι) (b : B) :
    ContMDiffOn (𝓘(ℝ, EB).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin a))) I ∞
      (S.nativeBundleChart i b).symm (S.nativeBundleChart i b).target :=
  S.contMDiffOn_coordinateBundleChart_symm (ContinuousLinearEquiv.refl ℝ EB) i b

/-- The joint lift with the literal original native base chart is smooth on its true domain. -/
theorem contMDiffOn_nativeBundleChart_jointLift (i : ι) (b : B) :
    ContMDiffOn (𝓘(ℝ, EB).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin a))) I ∞
      (fun z : EB × EuclideanSpace ℝ (Fin a) ↦
        S.fiberEuclideanLift i ((chartAt EB b).symm z.1) z.2)
      (S.nativeBundleBaseSet i b ×ˢ univ) := by
  simpa only [coordinateBundleChart_symm_apply, coordinateBundleBaseSet,
    principalTorusBaseCoordinateChart_refl, nativeBundleBaseSet, fiberEuclideanLift] using
    S.contMDiffOn_coordinateBundleChart_jointLift (ContinuousLinearEquiv.refl ℝ EB) i b

theorem isOpen_nativeBundleBaseSet (i : ι) (b : B) :
    IsOpen (S.nativeBundleBaseSet i b) :=
  (chartAt EB b).isOpen_inter_preimage_symm (S.trivialization i).open_baseSet

theorem nativeBundleChart_cover (x : M) :
    ∃ k : ι × B, x ∈ (S.nativeBundleChart k.1 k.2).source :=
  S.coordinateBundleChart_cover (ContinuousLinearEquiv.refl ℝ EB) x

/-- Original integer periodicity of the actual lifted source point, not an assumed data law. -/
theorem nativeBundleChart_jointLift_periodic (i : ι) (b : B) (p : EB)
    (y : EuclideanSpace ℝ (Fin a)) (n : Fin a → ℤ) :
    S.fiberEuclideanLift i ((chartAt EB b).symm p)
      (y + toLp 2 (fun j ↦ (n j : ℝ))) =
    S.fiberEuclideanLift i ((chartAt EB b).symm p) y := by
  have hq :
      toLp 2 (fun k ↦ ((y + toLp 2 (fun j ↦ (n j : ℝ))) k : AddCircle (1 : ℝ))) =
        toLp 2 (fun k ↦ (y k : AddCircle (1 : ℝ))) := by
    apply PiLp.ext
    intro k
    have hn : ((n k : ℝ) : AddCircle (1 : ℝ)) = 0 := by
      simp
    change ((y k + (n k : ℝ) : ℝ) : AddCircle (1 : ℝ)) = (y k : AddCircle (1 : ℝ))
    rw [AddCircle.coe_add, hn, add_zero]
  exact congrArg (S.fiberChartPoint i ((chartAt EB b).symm p)) hq

#print axioms nativeBundleChart_jointLift_periodic
#print axioms nativeBundleChart_source
#print axioms nativeBundleChart_target
#print axioms contMDiffOn_nativeBundleChart_jointLift
#print axioms contMDiffOn_coordinateBundleChart_jointLift
#print axioms coordinateBundleChart_source_pullback
#print axioms contMDiffOn_coordinateBundleChart
#print axioms contMDiffOn_coordinateBundleChart_symm
#print axioms principalTorusEuclideanModelEquiv
#print axioms contMDiffOn_principalTorusBaseCoordinateChart
#print axioms contMDiffOn_principalTorusBaseCoordinateChart_symm
#print axioms coordinateBundleChart_target
#print axioms coordinateBundleChart_cover
end PrincipalTorusBundle
end GlobalEmbedding.Paper
