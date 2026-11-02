import GlobalEmbedding.Paper.PeriodicFlatTorusProjectionSmooth
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Genuine parameter-times-flat-torus local smoothness is equivalent to lift smoothness

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, line 418.
DAG node: `balanced-holder-flat-torus-product-lift-at`.
-/

open Set WithLp IsManifold
open scoped Topology Manifold

open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Native joint manifold C^n at a parameter/torus point is equivalent to actual lift C^n.

Forward, compose with the actual smooth quotient projection. Reverse, use the actual quotient
local inverse through the prescribed lift, which is an actual smooth atlas member. Composing
the lift map with this local inverse agrees with the original function in a neighborhood,
by the actual inverse identity. No continuity of the original function is assumed.
Source: genuine joint torus/parameter smoothness in the proof of `lem:balanced`. -/
theorem periodic_flat_torus_product_lift_contMDiffAt_iff
    {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {a : ℕ} (n : ℕ∞ω)
    (f : P × PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ)) → V)
    (p : P) (x : EuclideanSpace ℝ (Fin a)) :
    let _charted := periodicFlatTorusChartedSpace a
    ContMDiffAt ((𝓘(ℝ, P)).prod (𝓘(ℝ, EuclideanSpace ℝ (Fin a)))) (𝓘(ℝ, V)) n f
        (p, toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ)))) ↔
      ContDiffAt ℝ n (fun z : P × EuclideanSpace ℝ (Fin a) ↦
        f (z.1, toLp 2 (fun i : Fin a ↦ (z.2 i : AddCircle (1 : ℝ)))) ) (p, x) := by
  dsimp only
  let _charted := periodicFlatTorusChartedSpace a
  have := periodic_flat_torus_isManifold a n
  let π := fun y : EuclideanSpace ℝ (Fin a) ↦
    toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ)))
  let F := fun z : P × EuclideanSpace ℝ (Fin a) ↦ f (z.1, π z.2)
  constructor
  · intro hf
    have hπ := (periodic_flat_torus_projection_contMDiff a n) x
    have hprod :=
      ((ContinuousLinearMap.fst ℝ P (EuclideanSpace ℝ (Fin a))).contMDiffAt (n := n)
        (x := (p, x))).prodMk
        (hπ.comp (p, x)
          (ContinuousLinearMap.snd ℝ P (EuclideanSpace ℝ (Fin a))).contMDiffAt)
    exact (hf.comp (p, x) hprod).contDiffAt
  · intro hf
    have hF : ContMDiffAt (𝓘(ℝ, P × EuclideanSpace ℝ (Fin a)))
        (𝓘(ℝ, V)) n F (p, x) := hf.contMDiffAt
    let hq := periodic_flat_torus_local_homeomorph (a := a)
    let e := hq.localInverseAt x
    have he : e ∈ atlas (EuclideanSpace ℝ (Fin a))
        (PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ))) := mem_range_self x
    have hx : π x ∈ e.source := hq.apply_self_mem_localInverseAt_source
    have hec := contMDiffAt_of_mem_maximalAtlas (n := n)
      (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin a))) (subset_maximalAtlas he) hx
    have hprod := (contMDiffAt_fst (I := 𝓘(ℝ, P))).prodMk_space
      (hec.comp (p, π x) contMDiffAt_snd)
    have hex : e (π x) = x := hq.localInverseAt_apply_self
    have hF' : ContMDiffAt (𝓘(ℝ, P × EuclideanSpace ℝ (Fin a)))
        (𝓘(ℝ, V)) n F (p, e (π x)) := by simpa only [hex] using hF
    apply (hF'.comp (p, π x) hprod).congr_of_eventuallyEq
    have hnear : ∀ᶠ z : P × PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ)) in 𝓝 (p, π x),
        z.2 ∈ e.source := continuous_snd.continuousAt.eventually (e.open_source.mem_nhds hx)
    filter_upwards [hnear] with z hz
    change f z = f (z.1, π (e z.2))
    have hcancel : π (e z.2) = z.2 :=
      (congrFun (hq.localInverseAt_symm x) (e z.2)).symm.trans (e.left_inv hz)
    rw [hcancel]

#print axioms periodic_flat_torus_product_lift_contMDiffAt_iff

end GlobalEmbedding.Paper
