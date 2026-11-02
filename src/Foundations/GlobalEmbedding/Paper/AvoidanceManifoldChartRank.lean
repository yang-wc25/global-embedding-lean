import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Actual chart smoothness and rank for finite-parameter avoidance

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:avoidance`,
proof lines 940–941. On an open manifold domain, the preferred chart gives an
ordinary smooth equation on an open model domain. The actual manifold derivative
and coordinate derivative have the same rank, through their actual tangent-model
continuous linear equivalences. No Hausdorff or global smoothness hypothesis is needed.
-/

open Manifold Set
open scoped ContDiff Topology

namespace GlobalEmbedding.Paper

/-- Ordinary smoothness in the actual preferred chart, and equality of the real
ranks of its ordinary derivative and the actual manifold derivative. Smoothness
is only required on the original open domain. The derivative formula uses both
native tangent-space identifications; surjectivity preserves the source image,
and the target linear equivalence preserves its dimension.
Source: local chart reduction in the proof of `lem:avoidance`. -/
theorem avoidance_manifold_chart_rank
    {A M F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [TopologicalSpace M] [ChartedSpace A M] [IsManifold 𝓘(ℝ, A) ∞ M]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {U : Set M} (hU : IsOpen U) {f : M → F}
    (hf : ContMDiffOn 𝓘(ℝ, A) 𝓘(ℝ, F) ∞ f U) {x : M} (hx : x ∈ U) :
    let e := chartAt A x
    let W := e.target ∩ e.symm ⁻¹' U
    IsOpen W ∧ e x ∈ W ∧ ContDiffOn ℝ ∞ (f ∘ e.symm) W ∧
      Module.finrank ℝ (LinearMap.range (fderiv ℝ (f ∘ e.symm) (e x)).toLinearMap) =
        Module.finrank ℝ (LinearMap.range
          (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, F) f x).toLinearMap) := by
  dsimp only
  let e := chartAt A x
  let W := e.target ∩ e.symm ⁻¹' U
  have hxe : x ∈ e.source := mem_chart_source A x
  have hxW : e x ∈ W := by
    refine ⟨e.map_source hxe, ?_⟩
    change e.symm (e x) ∈ U
    simpa only [e.left_inv hxe] using hx
  have he : ContMDiffOn 𝓘(ℝ, A) 𝓘(ℝ, A) ∞ e.symm e.target :=
    contMDiffOn_chart_symm
  have hf' : ContDiffOn ℝ ∞ (f ∘ e.symm) W :=
    (hf.comp (he.mono inter_subset_left) (fun z hz ↦ hz.2)).contDiffOn
  refine ⟨e.isOpen_inter_preimage_symm hU, hxW, hf', ?_⟩
  let D := fderiv ℝ (f ∘ e.symm) (e x)
  let src := tangentSpaceCastModel 𝓘(ℝ, A) x
  let tgt := tangentSpaceCastModel 𝓘(ℝ, F) (f x)
  have hfx := ((hf x hx).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hd : mfderiv 𝓘(ℝ, A) 𝓘(ℝ, F) f x =
      tgt.symm.toContinuousLinearMap.comp (D.comp src.toContinuousLinearMap) := by
    simpa [D, e, src, tgt, mfld_simps] using hfx.mfderiv
  have hsrc : (D.comp src.toContinuousLinearMap).range = D.range := by
    ext y
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨src v, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨src.symm v, by simp⟩
  change Module.finrank ℝ D.range = _
  rw [hd]
  change Module.finrank ℝ D.range = Module.finrank ℝ
    (LinearMap.range (tgt.symm.toLinearEquiv.toLinearMap.comp
      (D.comp src.toContinuousLinearMap).toLinearMap))
  rw [LinearMap.range_comp, hsrc]
  exact (tgt.symm.toLinearEquiv.finrank_map_eq D.range).symm

#print axioms avoidance_manifold_chart_rank

end GlobalEmbedding.Paper
