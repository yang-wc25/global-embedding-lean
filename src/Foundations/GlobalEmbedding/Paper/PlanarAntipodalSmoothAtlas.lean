import GlobalEmbedding.Paper.PlanarAntipodalQuotient
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Actual native smoothness of the antipodal quotient

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:planar`, lines258–259.
DAG node: `planar-antipodal-smooth-atlas`.
-/
noncomputable section
open scoped Manifold ContDiff Topology
open Set Filter
namespace GlobalEmbedding.Paper

/-- The genuine covering projection is a local homeomorphism. -/
abbrev planarAntipodalLocalHomeomorph (C : ℕ) :
    IsLocalHomeomorph (@planarAntipodalProjection C) :=
  (planarAntipodalProjection_quotientCovering C).isLocalHomeomorph

/-- A genuine local section, pulled to the sphere, is locally a single actual smooth
deck transformation. Thus its native smoothness is proved without assuming smoothness
of the quotient or of the projection. -/
theorem planarAntipodalLocalLift_contMDiffAt {C : ℕ} [Fact (0 < C)]
    (z₀ z : PlanarHopfSphere C)
    (hz : planarAntipodalProjection z ∈
      ((planarAntipodalLocalHomeomorph C).localInverseAt z₀).source) :
    ContMDiffAt (planarHopfModel C) (planarHopfModel C) ∞
      (fun w ↦ (planarAntipodalLocalHomeomorph C).localInverseAt z₀
        (planarAntipodalProjection w)) z := by
  let L := (planarAntipodalLocalHomeomorph C).localInverseAt z₀
  obtain ⟨u, hu⟩ := (planarAntipodalProjection_quotientCovering C).apply_eq_iff_mem_orbit.mp
    ((planarAntipodalLocalHomeomorph C).apply_localInverseAt_of_mem hz)
  change u • z = L (planarAntipodalProjection z) at hu
  have huL : u • z ∈ L.target := by
    rw [hu]
    exact L.map_source hz
  have he : (fun w ↦ L (planarAntipodalProjection w)) =ᶠ[𝓝 z] (fun w ↦ u • w) := by
    filter_upwards [(continuous_const_smul u).continuousAt
      (L.open_target.mem_nhds huL)] with w hw
    have hh := L.right_inv hw
    simpa only [L, IsLocalHomeomorph.localInverseAt_symm,
      (planarAntipodalProjection_quotientCovering C).map_smul u] using hh
  exact (planarAntipodalDeck_contMDiff C u).contMDiffAt.congr_of_eventuallyEq he

/-- The actual pulled antipodal quotient atlas has native smooth transition maps.
The proof reduces each transition to a sphere chart, a locally fixed smooth deck
map, and a sphere inverse chart. No desired smooth-quotient hypothesis occurs. -/
instance planarRealProjectiveIsManifold (C : ℕ) [Fact (0 < C)] :
    IsManifold (planarHopfModel C) ∞ (PlanarRealProjective C) := by
  let H := EuclideanSpace ℝ (Fin (2 * C - 1))
  let σ : PlanarRealProjective C → PlanarHopfSphere C :=
    (planarAntipodalProjection_surjective C).hasRightInverse.choose
  let hf := planarAntipodalLocalHomeomorph C
  apply isManifold_of_contDiffOn
  intro e e' he he'
  change ∃ q : PlanarRealProjective C,
    (hf.localInverseAt (σ q)).trans (chartAt H (σ q)) = e at he
  change ∃ q : PlanarRealProjective C,
    (hf.localInverseAt (σ q)).trans (chartAt H (σ q)) = e' at he'
  obtain ⟨q, rfl⟩ := he
  obtain ⟨q', rfl⟩ := he'
  let c := chartAt H (σ q)
  let c' := chartAt H (σ q')
  let L := hf.localInverseAt (σ q)
  let L' := hf.localInverseAt (σ q')
  simp only [planarHopfModel, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, Set.preimage_id, Set.range_id, Set.inter_univ]
  change ContDiffOn ℝ ∞ ((L.trans c).symm.trans (L'.trans c'))
    ((L.trans c).symm.trans (L'.trans c')).source
  simp only [OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.coe_trans_symm,
    L, IsLocalHomeomorph.localInverseAt_symm]

  intro v hv
  have hv₀ : v ∈ c.target := hv.1.1
  have hv₁ : planarAntipodalProjection (c.symm v) ∈ L'.source := by
    simpa only [OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.symm_target,
      Function.comp_apply, Set.mem_preimage, OpenPartialHomeomorph.coe_trans_symm,
      L, hf, IsLocalHomeomorph.localInverseAt_symm] using hv.2.1
  have hv₂ : L' (planarAntipodalProjection (c.symm v)) ∈ c'.source := by
    simpa only [OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.symm_target,
      Function.comp_apply, Set.mem_preimage, OpenPartialHomeomorph.coe_trans_symm,
      L, hf, IsLocalHomeomorph.localInverseAt_symm] using hv.2.2
  have hc : ContMDiffAt (planarHopfModel C) (planarHopfModel C) ∞ c.symm v :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (σ q)) hv₀
  have hL := planarAntipodalLocalLift_contMDiffAt (σ q') (c.symm v) hv₁
  have hc' : ContMDiffAt (planarHopfModel C) (planarHopfModel C) ∞ c'
      (L' (planarAntipodalProjection (c.symm v))) :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (σ q')) hv₂
  have hh := hc'.comp v (hL.comp v hc)
  exact hh.contDiffAt.contDiffWithinAt

/-- The genuine quotient projection is native smooth for the actual quotient atlas. -/
theorem planarAntipodalProjection_contMDiff (C : ℕ) [Fact (0 < C)] :
    ContMDiff (planarHopfModel C) (planarHopfModel C) ∞
      (@planarAntipodalProjection C) := by
  intro z
  rw [contMDiffAt_iff_target]
  refine ⟨(planarAntipodalProjection_quotientCovering C).continuous.continuousAt, ?_⟩
  let H := EuclideanSpace ℝ (Fin (2 * C - 1))
  let σ : PlanarRealProjective C → PlanarHopfSphere C :=
    (planarAntipodalProjection_surjective C).hasRightInverse.choose
  let z₀ := σ (planarAntipodalProjection z)
  let hf := planarAntipodalLocalHomeomorph C
  let L := hf.localInverseAt z₀
  have hσ : planarAntipodalProjection z₀ = planarAntipodalProjection z :=
    (planarAntipodalProjection_surjective C).hasRightInverse.choose_spec _
  have hz : planarAntipodalProjection z ∈ L.source := by
    rw [← hσ]
    exact hf.apply_self_mem_localInverseAt_source
  have hLz : L (planarAntipodalProjection z) = z₀ := by
    rw [← hσ]
    exact hf.localInverseAt_apply_self
  have hchart : L (planarAntipodalProjection z) ∈ (chartAt H z₀).source := by
    rw [hLz]
    exact ChartedSpace.mem_chart_source _
  have hh := (contMDiffAt_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := planarHopfModel C) (n := ∞) z₀) hchart).comp z
      (planarAntipodalLocalLift_contMDiffAt z₀ z hz)
  change ContMDiffAt (planarHopfModel C) 𝓘(ℝ, H) ∞
    (fun w ↦ (planarHopfModel C) ((chartAt H z₀) (L (planarAntipodalProjection w)))) z
  exact (planarHopfModel C).contMDiff.contMDiffAt.comp z hh

/-- Native smoothness at a quotient point can be checked on an actual local lift.
This criterion refers to the literal projection and its proved smooth native atlas. -/
theorem planarAntipodal_contMDiffAt_of_pullback {C : ℕ} [Fact (0 < C)]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners ℝ E' H')
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    (f : PlanarRealProjective C → N) (x : PlanarRealProjective C)
    (hf : ∀ z : PlanarHopfSphere C, planarAntipodalProjection z = x →
      ContMDiffAt (planarHopfModel C) I' ∞ (fun w ↦ f (planarAntipodalProjection w)) z) :
    ContMDiffAt (planarHopfModel C) I' ∞ f x := by
  let σ : PlanarRealProjective C → PlanarHopfSphere C :=
    (planarAntipodalProjection_surjective C).hasRightInverse.choose
  let z₀ := σ x
  let L := (planarAntipodalLocalHomeomorph C).localInverseAt z₀
  have hz₀ : planarAntipodalProjection z₀ = x :=
    (planarAntipodalProjection_surjective C).hasRightInverse.choose_spec x
  have hLx : L x = z₀ := by
    rw [← hz₀]
    exact (planarAntipodalLocalHomeomorph C).localInverseAt_apply_self
  have hxchart : extChartAt (planarHopfModel C) x x =
      extChartAt (planarHopfModel C) z₀ z₀ := by
    change (planarHopfModel C) ((chartAt _ z₀) (L x)) =
      (planarHopfModel C) ((chartAt _ z₀) z₀)
    rw [hLx]
  have hsymm : (extChartAt (planarHopfModel C) x).symm =
      (fun v ↦ planarAntipodalProjection ((extChartAt (planarHopfModel C) z₀).symm v)) := by
    funext v
    change L.symm ((chartAt _ z₀).symm ((planarHopfModel C).symm v)) = _
    exact congrFun ((planarAntipodalLocalHomeomorph C).localInverseAt_symm z₀) _
  rw [contMDiffAt_iff_source, hxchart, hsymm]
  change ContMDiffWithinAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * C - 1))) I' ∞
    ((fun w : PlanarHopfSphere C ↦ f (planarAntipodalProjection w)) ∘
      (extChartAt (planarHopfModel C) z₀).symm)
    (Set.range (planarHopfModel C)) (extChartAt (planarHopfModel C) z₀ z₀)
  exact (hf z₀ hz₀).comp_contMDiffWithinAt_of_eq
    (contMDiffWithinAt_extChartAt_symm_range_self (I := planarHopfModel C) z₀)
    (extChartAt_to_inv z₀)

/-- Each genuine covering local inverse is native smooth on its actual open domain. -/
theorem planarAntipodalLocalInverse_contMDiffOn {C : ℕ} [Fact (0 < C)]
    (z₀ : PlanarHopfSphere C) :
    ContMDiffOn (planarHopfModel C) (planarHopfModel C) ∞
      ((planarAntipodalLocalHomeomorph C).localInverseAt z₀)
      ((planarAntipodalLocalHomeomorph C).localInverseAt z₀).source := by
  intro x hx
  apply ContMDiffAt.contMDiffWithinAt
  apply planarAntipodal_contMDiffAt_of_pullback (planarHopfModel C)
  intro z hz
  apply planarAntipodalLocalLift_contMDiffAt z₀ z
  simpa only [hz] using hx

/-- An actual map from the quotient is native smooth exactly when its pullback to
the actual sphere is native smooth. This is the genuine covering descent criterion. -/
theorem planarAntipodal_contMDiff_iff_pullback {C : ℕ} [Fact (0 < C)]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners ℝ E' H')
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    (f : PlanarRealProjective C → N) :
    ContMDiff (planarHopfModel C) I' ∞ f ↔
      ContMDiff (planarHopfModel C) I' ∞ (fun z ↦ f (planarAntipodalProjection z)) := by
  constructor
  · intro hf
    exact hf.comp (planarAntipodalProjection_contMDiff C)
  · intro hf x
    exact planarAntipodal_contMDiffAt_of_pullback I' f x (fun z _ ↦ hf z)

end GlobalEmbedding.Paper
