import Round2.AtlasNormGeometry

/-!
# Every fixed finite jet order on the same actual compact chart overlaps

The C² atlas comparison already constructed the literal transition, its open
domain and the compact support intersection.  Here that same geometry supplies
one bound for all transition jets up to any fixed order.  This is needed to
transport the original C¹/C² parameter bounds and spatial C³ probe bound
between two fixed atlases, without constructing a second probe family.
-/

noncomputable section
open Manifold Set
open scoped ContDiff Topology

namespace GlobalEmbedding.Upgrade
open Paper

variable {n : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- All derivatives through the fixed order are bounded on the actual
compact overlap.  The constant precedes every later map, parameter and scale.
The finite order set and the compact overlap may have no positive-order or
no spatial points, respectively; no nonempty premise is needed. -/
theorem exists_atlasNormTransition_finiteJet_bound
    (order : ℕ) (A B : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hB : IsSmoothBufferedAtlas B)
    (hAc : ∀ i, IsCompact (A.support i))
    (hBc : ∀ j, IsCompact (B.support j)) (i : Fin A.count) (j : Fin B.count) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ z ∈ atlasNormOverlapSupport A B i j,
      ∀ a ≤ order, ‖iteratedFDeriv ℝ a (atlasNormTransition A B i j) z‖ ≤ D := by
  classical
  have hs := atlasNormTransition_contDiffOn A B hA hB i j
  have ho := atlasNormTransitionDomain_isOpen A B i j
  have hc := atlasNormOverlapSupport_isCompact A B hB hAc hBc i j
  have hsub := atlasNormOverlapSupport_subset_domain A B hA hB i j
  choose C hC using fun a : Fin (order + 1) ↦ hc.exists_bound_of_continuousOn
    ((ContinuousOn.continuousOn_iteratedFDeriv hs ho (k := a.val) (by simp)).mono hsub)
  obtain ⟨Cmax, hCmax⟩ := Finite.exists_le C
  refine ⟨|Cmax| + 1, by linarith [abs_nonneg Cmax], ?_⟩
  intro z hz a ha
  exact (hC ⟨a, by omega⟩ z hz).trans ((hCmax ⟨a, by omega⟩).trans
    (by linarith [le_abs_self Cmax]))

end GlobalEmbedding.Upgrade
