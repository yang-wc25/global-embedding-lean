import GlobalEmbedding.External.SphereEversion.Global.OneJetBundle
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# Genuine smooth native one-jet evaluation on a tangent field

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:planar`, lines 256–260.
This is the common native evaluation step in the open maps relations for both the framed
partial immersion and the reflection-equivariant initial planar map.
-/

noncomputable section

open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- Internal native evaluation bridge for proving openness of the actual initial-map relation.
It applies the genuine jet derivative to the genuine smooth field and then uses the canonical
normed-space tangent identification. No coordinate evaluation is assumed as additional data. -/
theorem contMDiff_oneJetFieldEval
    {V H M F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace H] {I : ModelWithCorners ℝ V H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (X : ContMDiffSection I V ∞ (TangentSpace I : M → Type _)) :
    ContMDiff ((I.prod 𝓘(ℝ, F)).prod 𝓘(ℝ, V →L[ℝ] F)) 𝓘(ℝ, F) ∞
      (fun σ : OneJetBundle I M 𝓘(ℝ, F) F ↦
        NormedSpace.fromTangentSpace σ.1.2 (σ.2 (X σ.1.1))) := by
  let J := (I.prod 𝓘(ℝ, F)).prod 𝓘(ℝ, V →L[ℝ] F)
  intro σ
  have hj := (contMDiffAt_oneJetBundle (I := I) (I' := 𝓘(ℝ, F)) (J := J)
    (M := M) (M' := F) (N := OneJetBundle I M 𝓘(ℝ, F) F)
    (f := fun τ : OneJetBundle I M 𝓘(ℝ, F) F ↦ τ) (x₀ := σ)).mp
    (contMDiffAt_id : ContMDiffAt J J ∞ (id : OneJetBundle I M 𝓘(ℝ, F) F → _) σ)
  have hv := (X.contMDiff (σ.1.1)).comp σ hj.1
  have hφ := hj.2.2
  unfold inTangentCoordinates at hφ
  have he : ContMDiffAt J (𝓘(ℝ, F)).tangent ∞
      (fun τ : OneJetBundle I M 𝓘(ℝ, F) F ↦
        Bundle.TotalSpace.mk' F τ.1.2 (τ.2 (X τ.1.1))) σ :=
    ContMDiffAt.clm_apply_of_inCoordinates (𝕜 := ℝ) (F₁ := V) (F₂ := F)
      (B₁ := M) (B₂ := F) (E₁ := TangentSpace I) (E₂ := TangentSpace 𝓘(ℝ, F))
      (IB₁ := I) (IB₂ := 𝓘(ℝ, F)) (IM := J)
      (b₁ := fun τ : OneJetBundle I M 𝓘(ℝ, F) F ↦ τ.1.1)
      (b₂ := fun τ : OneJetBundle I M 𝓘(ℝ, F) F ↦ τ.1.2)
      (ϕ := fun τ : OneJetBundle I M 𝓘(ℝ, F) F ↦ τ.2)
      (v := fun τ : OneJetBundle I M 𝓘(ℝ, F) F ↦ X τ.1.1) hφ hv hj.2.1
  exact ((contMDiff_snd_tangentBundle_modelSpace F 𝓘(ℝ, F)
    (n := (∞ : WithTop ℕ∞))) _).comp σ he

#print axioms contMDiff_oneJetFieldEval

end GlobalEmbedding.Paper
