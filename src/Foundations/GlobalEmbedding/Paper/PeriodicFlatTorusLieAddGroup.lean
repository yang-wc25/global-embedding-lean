import GlobalEmbedding.Paper.PeriodicFlatTorusBinarySmoothDescent
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# The original flat torus is a genuine native smooth and analytic additive Lie group

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, line 418.
DAG node: `balanced-holder-flat-torus-lie-add-group`.
-/

open WithLp
open scoped Manifold

open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- The original flat-torus addition and negation give a native LieAddGroup at every order.

Actual addition is specified by the genuine Euclidean lift (x,y)↦x+y. Actual binary negation
is specified by (x,y)↦−x; compose it with q↦(q,0). Both genuine smooth lifts descend by the
proved actual binary lifting theorem. Combine these actual operation proofs with the proved
actual atlas compatibility. The original group operations, topology and metric are retained;
this explicit theorem does not install a global instance.
Source: smooth torus translations and chart changes in the proof of `lem:balanced`. -/
theorem periodic_flat_torus_lieAddGroup (a : ℕ) (n : ℕ∞ω) :
    let _charted := periodicFlatTorusChartedSpace a
    LieAddGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin a))) n
      (PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ))) := by
  dsimp only
  let _charted := periodicFlatTorusChartedSpace a
  have := periodic_flat_torus_isManifold a n
  have hadd : ContMDiff ((𝓘(ℝ, EuclideanSpace ℝ (Fin a))).prod
      (𝓘(ℝ, EuclideanSpace ℝ (Fin a)))) (𝓘(ℝ, EuclideanSpace ℝ (Fin a))) n
      (fun z : (PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ))) ×
        (PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ))) ↦ z.1 + z.2) := by
    apply periodic_flat_torus_binary_descend_contMDiff n _
      (fun z : EuclideanSpace ℝ (Fin a) × EuclideanSpace ℝ (Fin a) ↦ z.1 + z.2)
      (contDiff_fst.add contDiff_snd)
    intro x y
    ext i
    change (x i : AddCircle (1 : ℝ)) + (y i : AddCircle (1 : ℝ)) =
      ((x i + y i : ℝ) : AddCircle (1 : ℝ))
    rw [AddCircle.coe_add]
  have hneg2 : ContMDiff ((𝓘(ℝ, EuclideanSpace ℝ (Fin a))).prod
      (𝓘(ℝ, EuclideanSpace ℝ (Fin a)))) (𝓘(ℝ, EuclideanSpace ℝ (Fin a))) n
      (fun z : (PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ))) ×
        (PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ))) ↦ -z.1) := by
    apply periodic_flat_torus_binary_descend_contMDiff n _
      (fun z : EuclideanSpace ℝ (Fin a) × EuclideanSpace ℝ (Fin a) ↦ -z.1)
      contDiff_fst.neg
    intro x y
    ext i
    change -(x i : AddCircle (1 : ℝ)) = ((-x i : ℝ) : AddCircle (1 : ℝ))
    rw [AddCircle.coe_neg]
  have hneg : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin a)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin a))) n
      (fun q : PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ)) ↦ -q) :=
    hneg2.comp (contMDiff_id.prodMk (contMDiff_const (c := 0)))
  exact
    { toContMDiffAdd :=
        { toIsManifold := periodic_flat_torus_isManifold a n
          contMDiff_add := hadd }
      contMDiff_neg := hneg }

#print axioms periodic_flat_torus_lieAddGroup

end GlobalEmbedding.Paper
