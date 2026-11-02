import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! An actual compact parameter cutoff. A compact evaluation set inside the
original open parameter region admits a smooth beta which is exactly one on a
fixed open neighborhood and compactly supported inside that region. Its entire
jet profile is produced before every later scale. No compactness of all Ep is
asserted, including in positive parameter dimension. -/

noncomputable section
open Manifold Set Function Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem actual_compact_parameter_cutoff
    (K Omega : Set E) (hK : IsCompact K) (hOmega : IsOpen Omega) (hKO : K ⊆ Omega) :
    ∃ (beta : E → ℝ) (V C : Set E) (B : ℕ → ℝ),
      ContDiff ℝ ∞ beta ∧ IsOpen V ∧ K ⊆ V ∧ V ⊆ Omega ∧
      IsCompact C ∧ tsupport beta ⊆ C ∧ C ⊆ Omega ∧
      (∀ p ∈ V, beta p = 1) ∧ (∀ p, beta p ∈ Icc 0 1) ∧
      (∀ j, 0 ≤ B j) ∧ ∀ j p, ‖iteratedFDeriv ℝ j beta p‖ ≤ B j := by
  obtain ⟨C,hC,hCclosed,hKC,hCO⟩ := exists_compact_closed_between hK hOmega hKO
  obtain ⟨beta,hOne,hZero,hRange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (𝓘(ℝ,E)) hK.isClosed hKC (n := ⊤)
  obtain ⟨V,hV,hKV,hVOne⟩ := eventually_nhdsSet_iff_exists.mp hOne
  have hSupport : tsupport (beta : E → ℝ) ⊆ C := by
    apply closure_minimal _ hCclosed
    intro p hp
    by_contra hpC
    exact hp (hZero p hpC)
  have hBetaCompact : HasCompactSupport (beta : E → ℝ) :=
    hC.of_isClosed_subset (isClosed_tsupport _) hSupport
  have hSmooth : ContDiff ℝ ∞ (beta : E → ℝ) := beta.contMDiff.contDiff
  have hJets (j : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ p, ‖iteratedFDeriv ℝ j (beta : E → ℝ) p‖ ≤ B := by
    obtain ⟨B,hB,hBounds⟩ := hBetaCompact.exists_bound_iteratedFDeriv hSmooth j
    exact ⟨B,hB,hBounds j le_rfl⟩
  choose B hB hJets using hJets
  refine ⟨beta,V ∩ Omega,C,B,hSmooth,hV.inter hOmega,
    (fun p hp => ⟨hKV hp,hKO hp⟩),inter_subset_right,hC,hSupport,hCO,?_,hRange,hB,hJets⟩
  intro p hp
  exact hVOne p hp.1

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_compact_parameter_cutoff
