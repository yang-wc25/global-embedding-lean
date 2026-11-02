import GlobalEmbedding.Paper.PeriodicFlatTorusProjection
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# The actual flat torus projection is a local homeomorphism

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, line 418.
DAG node: `balanced-holder-flat-torus-local-homeomorph`.
-/

open WithLp

namespace GlobalEmbedding.Paper

/-- The actual Euclidean-to-L2-flat-torus projection is a local homeomorphism.

Each real-to-period-one-circle projection is a local homeomorphism by Mathlib's actual
covering theorem. Take their finite product open partial homeomorphism at each point and
transport through the original PiLp homeomorphisms. The spaces, projection and flat metric
are exactly those used by the actual Holder norm and translations, including dimension zero.
Source: local torus lift parameters in the proof of `lem:balanced`. -/
theorem periodic_flat_torus_local_homeomorph {a : ℕ} :
    IsLocalHomeomorph (fun x : EuclideanSpace ℝ (Fin a) ↦
      toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ)))) := by
  classical
  have hpi : IsLocalHomeomorph (fun x : Fin a → ℝ ↦
      fun i ↦ (x i : AddCircle (1 : ℝ))) := by
    intro x
    choose e he hfun using fun i : Fin a ↦ (AddCircle.isLocalHomeomorph_coe (1 : ℝ)) (x i)
    refine ⟨OpenPartialHomeomorph.pi e, ?_, ?_⟩
    · exact fun i hi ↦ he i
    · funext y i
      exact congrFun (hfun i) (y i)
  exact (PiLp.homeomorph 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ))).symm.isLocalHomeomorph.comp
    (hpi.comp (PiLp.homeomorph 2 (fun _ : Fin a ↦ ℝ)).isLocalHomeomorph)

#print axioms periodic_flat_torus_local_homeomorph

end GlobalEmbedding.Paper
