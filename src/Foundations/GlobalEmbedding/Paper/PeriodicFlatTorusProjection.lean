import GlobalEmbedding.Paper.PeriodicFlatTorusDistance
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Constructions

/-!
# The actual Euclidean-to-flat-torus open quotient projection

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 382–418.
DAG node: `balanced-holder-flat-torus-projection`.
-/

open WithLp

namespace GlobalEmbedding.Paper

/-- Coordinate projection from Euclidean lifts to the actual L2 flat torus is an open quotient.

Proof: each real-to-period-one-circle projection is an open quotient. Products of open
quotients remain open quotients, and the PiLp product topologies are transported by the
canonical homeomorphisms. Source: the flat torus in the proof of `lem:balanced`. -/
theorem periodic_flat_torus_projection {a : ℕ} :
    IsOpenQuotientMap (fun x : EuclideanSpace ℝ (Fin a) ↦
      toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ)))) := by
  have hq : IsOpenQuotientMap (fun x : Fin a → ℝ ↦
      fun i ↦ (x i : AddCircle (1 : ℝ))) :=
    IsOpenQuotientMap.piMap (fun i ↦ QuotientAddGroup.isOpenQuotientMap_mk)
  exact (PiLp.homeomorph 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ))).symm.isOpenQuotientMap.comp
    (hq.comp (PiLp.homeomorph 2 (fun _ : Fin a ↦ ℝ)).isOpenQuotientMap)

#print axioms periodic_flat_torus_projection

end GlobalEmbedding.Paper
