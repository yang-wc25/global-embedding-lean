import GlobalEmbedding.Paper.PeriodicFlatTorusLocalHomeomorph

/-!
# Continuous lifts of the same actual flat torus map differ locally by a constant

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, line 418.
DAG node: `balanced-holder-flat-torus-lifts-locally-constant`.
-/

open Set WithLp
open scoped Topology

namespace GlobalEmbedding.Paper

/-- Continuous actual Euclidean lifts with the same torus projection have locally constant
vector difference on an open parameter domain.

The difference projects to zero. At its value at a parameter point, the actual projection
is injective on an open neighborhood, since it is a local homeomorphism. Continuity places
nearby differences in that same neighborhood. Their equal zero projections force equality.
Source: local torus lift and overlap translations in the proof of `lem:balanced`. -/
theorem periodic_flat_torus_lifts_eventually_sub_eq
    {P : Type*} [TopologicalSpace P] {a : ℕ} (U : Set P) (hU : IsOpen U)
    (F G : P → EuclideanSpace ℝ (Fin a)) (hF : ContinuousOn F U) (hG : ContinuousOn G U)
    (hπ : ∀ p ∈ U, toLp 2 (fun i : Fin a ↦ (F p i : AddCircle (1 : ℝ))) =
      toLp 2 (fun i : Fin a ↦ (G p i : AddCircle (1 : ℝ)))) (p : P) (hp : p ∈ U) :
    ∀ᶠ q in 𝓝 p, F q - G q = F p - G p := by
  let π := fun x : EuclideanSpace ℝ (Fin a) ↦
    toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ)))
  have hz (q : P) (hq : q ∈ U) : π (F q - G q) = 0 := by
    ext i
    change ((F q i - G q i : ℝ) : AddCircle (1 : ℝ)) = 0
    rw [AddCircle.coe_sub]
    exact sub_eq_zero.mpr (congrArg (fun z ↦ z i) (hπ q hq))
  obtain ⟨V, hV, hVp, hinj⟩ :=
    periodic_flat_torus_local_homeomorph.isLocallyInjective (F p - G p)
  have hc : ContinuousAt (fun q ↦ F q - G q) p :=
    (hF.continuousAt (hU.mem_nhds hp)).sub (hG.continuousAt (hU.mem_nhds hp))
  have hnear : ∀ᶠ q in 𝓝 p, F q - G q ∈ V := hc.eventually (hV.mem_nhds hVp)
  filter_upwards [hU.mem_nhds hp, hnear] with q hq hqV
  exact hinj hqV hVp ((hz q hq).trans (hz p hp).symm)

#print axioms periodic_flat_torus_lifts_eventually_sub_eq

end GlobalEmbedding.Paper
