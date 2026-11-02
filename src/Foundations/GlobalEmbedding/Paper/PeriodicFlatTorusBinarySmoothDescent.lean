import GlobalEmbedding.Paper.PeriodicFlatTorusProjectionSmooth
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Genuine binary flat-torus smooth descent from an actual Euclidean lift

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, line 418.
DAG node: `balanced-holder-flat-torus-binary-smooth-descent`.
-/

open Set WithLp IsManifold
open scoped Topology Manifold

open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- A genuine C^n Euclidean lift specifying an actual binary torus map makes it native C^n.

At each actual torus pair choose genuine local quotient inverses through actual lifts.
They are members of the actual smooth atlas. Their product is a native smooth local map
into the real vector product. Composing the actual smooth lifted map with the original
smooth quotient agrees with f on an actual neighborhood, by the specified lift identity
and the genuine local inverse identities. No continuity of f is assumed separately.
Source: smooth torus translation operations in the proof of `lem:balanced`. -/
theorem periodic_flat_torus_binary_descend_contMDiff {a : ℕ} (n : ℕ∞ω)
    (f : (PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ))) ×
      (PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ))) →
        PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ)))
    (G : EuclideanSpace ℝ (Fin a) × EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin a))
    (hG : ContDiff ℝ n G)
    (hfg : ∀ x y : EuclideanSpace ℝ (Fin a),
      f (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))),
        toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ)))) =
      toLp 2 (fun i : Fin a ↦ (G (x, y) i : AddCircle (1 : ℝ)))) :
    let _charted := periodicFlatTorusChartedSpace a
    ContMDiff ((𝓘(ℝ, EuclideanSpace ℝ (Fin a))).prod
      (𝓘(ℝ, EuclideanSpace ℝ (Fin a)))) (𝓘(ℝ, EuclideanSpace ℝ (Fin a))) n f := by
  dsimp only
  let _charted := periodicFlatTorusChartedSpace a
  have := periodic_flat_torus_isManifold a n
  let π := fun x : EuclideanSpace ℝ (Fin a) ↦
    toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ)))
  have hF := (periodic_flat_torus_projection_contMDiff a n).comp hG.contMDiff
  let hf := periodic_flat_torus_local_homeomorph (a := a)
  intro z
  obtain ⟨x, hx⟩ := periodic_flat_torus_projection.surjective z.1
  obtain ⟨y, hy⟩ := periodic_flat_torus_projection.surjective z.2
  change π x = z.1 at hx
  change π y = z.2 at hy
  let e1 := hf.localInverseAt x
  let e2 := hf.localInverseAt y
  have he1 : e1 ∈ atlas (EuclideanSpace ℝ (Fin a))
      (PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ))) := mem_range_self x
  have he2 : e2 ∈ atlas (EuclideanSpace ℝ (Fin a))
      (PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ))) := mem_range_self y
  have hxs : z.1 ∈ e1.source := by
    have h := hf.apply_self_mem_localInverseAt_source (x := x)
    change π x ∈ e1.source at h
    rwa [hx] at h
  have hys : z.2 ∈ e2.source := by
    have h := hf.apply_self_mem_localInverseAt_source (x := y)
    change π y ∈ e2.source at h
    rwa [hy] at h
  have hc1 := contMDiffAt_of_mem_maximalAtlas (n := n)
    (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin a))) (subset_maximalAtlas he1) hxs
  have hc2 := contMDiffAt_of_mem_maximalAtlas (n := n)
    (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin a))) (subset_maximalAtlas he2) hys
  have hlocal := (hc1.comp z contMDiffAt_fst).prodMk_space (hc2.comp z contMDiffAt_snd)
  apply ((hF (e1 z.1, e2 z.2)).comp z hlocal).congr_of_eventuallyEq
  have hnear1 : ∀ᶠ w in 𝓝 z, w.1 ∈ e1.source :=
    continuous_fst.continuousAt.eventually (e1.open_source.mem_nhds hxs)
  have hnear2 : ∀ᶠ w in 𝓝 z, w.2 ∈ e2.source :=
    continuous_snd.continuousAt.eventually (e2.open_source.mem_nhds hys)
  filter_upwards [hnear1, hnear2] with w hw1 hw2
  have hp1 : π (e1 w.1) = w.1 :=
    (congrFun (hf.localInverseAt_symm x) (e1 w.1)).symm.trans (e1.left_inv hw1)
  have hp2 : π (e2 w.2) = w.2 :=
    (congrFun (hf.localInverseAt_symm y) (e2 w.2)).symm.trans (e2.left_inv hw2)
  have heq := hfg (e1 w.1) (e2 w.2)
  change f (π (e1 w.1), π (e2 w.2)) = π (G (e1 w.1, e2 w.2)) at heq
  rw [hp1, hp2] at heq
  exact heq

#print axioms periodic_flat_torus_binary_descend_contMDiff

end GlobalEmbedding.Paper
