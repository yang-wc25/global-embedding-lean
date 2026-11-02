import Upgrade.CompactTrueRank

/-!
# Protecting the recomputed actual rank locus after the first avoidance

The map `F` in this theorem is the output of the current exact-metric
perturbation.  Its own `trueSecondForm` determines the protected set; the proof
does not reuse the reference map's old rank locus.  An actual open buffer of
the remaining compact source is constructed at the same time.
-/

noncomputable section

open Set Bundle Manifold Topology GlobalEmbedding.Paper
open scoped ContDiff

namespace GlobalEmbedding.Upgrade

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [CompactSpace M] [T2Space M] {N : ℕ}

/-- After actual rank-coincidence elimination, construct the protected
neighborhood and a buffered compact complement.  The original actual rank is
strictly greater than `q` on the closure of the buffer.  Empty bad locus,
empty source, and cross-component pairs require no exceptional assumptions. -/
theorem exists_current_trueRank_protected_complement
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (himm : ∀ z, Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F z))
    (q : ℕ) {P : Set (M × M)} (hP : IsCompact P)
    (hsym : ∀ x y, (x, y) ∈ P → (y, x) ∈ P)
    (hseparated : ∀ x y, (x, y) ∈ P →
      Module.finrank ℝ (trueSecondForm F hF x).range ≤ q → F x ≠ F y) :
    ∃ O W : Set M, IsOpen O ∧ IsOpen W ∧
      {x | Module.finrank ℝ (trueSecondForm F hF x).range ≤ q} ⊆ O ∧
      IsCompact Oᶜ ∧ Oᶜ ⊆ W ∧ IsCompact (closure W) ∧
      (∀ x ∈ closure W, q < Module.finrank ℝ (trueSecondForm F hF x).range) ∧
      ∃ d > 0, ∀ z ∈ P, z.1 ∈ closure O ∨ z.2 ∈ closure O →
        d < ‖F z.1 - F z.2‖ := by
  let S := {x | Module.finrank ℝ (trueSecondForm F hF x).range ≤ q}
  have hSclosed : IsClosed S := isClosed_trueSecondForm_finrank_le F hF himm q
  have hS : IsCompact S := hSclosed.isCompact
  have hsep : ∀ z ∈ P, z.1 ∈ S ∨ z.2 ∈ S → F z.1 ≠ F z.2 := by
    intro z hz hbad
    rcases hbad with hx | hy
    · exact hseparated z.1 z.2 hz hx
    · exact (hseparated z.2 z.1 (hsym z.1 z.2 hz) hy).symm
  obtain ⟨O, hO, hSO, d, hd, hgap⟩ :=
    exists_protected_pair_neighborhood hP hS hF.continuous hsep
  have hC : IsCompact Oᶜ := hO.isClosed_compl.isCompact
  have hCS : Oᶜ ⊆ Sᶜ := compl_subset_compl.mpr hSO
  obtain ⟨W, hW, hCW, hWS, hWcompact⟩ :=
    exists_open_between_and_isCompact_closure hC hSclosed.isOpen_compl hCS
  refine ⟨O, W, hO, hW, hSO, hC, hCW, hWcompact, ?_, d, hd, hgap⟩
  intro x hx
  exact Nat.lt_of_not_ge (hWS hx)

end GlobalEmbedding.Upgrade
