import Upgrade.CompactTrueRank
import Upgrade.SupportedActualLocus
import GlobalEmbedding.Paper.ImmersionNormalRank

/-!
# The recomputed supported locus and its protected compact complement

The supported predicate below is applied to the current map's own actual
second form.  Relative closedness comes from the accepted supported-locus
theorem through the actual normal coordinates constructed in this candidate.
In dimension three only supported coincidences need be absent; the supported
locus itself can be nonempty and is protected by an open neighborhood.
-/

noncomputable section
open Set Bundle Manifold Topology GlobalEmbedding.Paper
open scoped ContDiff

namespace GlobalEmbedding.Upgrade

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {N : ℕ}

/-- Surjectivity is the original actual rank threshold, using the normal
dimension of the same immersion at each point. -/
theorem trueSecondForm_surjective_iff_finrank_ge
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (x : M) (himm : Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F x)) :
    Function.Surjective (trueSecondForm F hF x) ↔
      N - Module.finrank ℝ E ≤ Module.finrank ℝ (trueSecondForm F hF x).range := by
  rw [← immersion_normal_rank F x himm]
  constructor
  · intro h
    rw [LinearMap.range_eq_top.mpr h, finrank_top]
  · intro h
    apply LinearMap.range_eq_top.mp
    exact Submodule.eq_top_of_finrank_eq
      (le_antisymm (trueSecondForm F hF x).range.finrank_le h)

/-- The full-rank locus is open in the actual source; no normal trivialization
or continuity of an independently supplied matrix field is assumed. -/
theorem isOpen_trueSecondForm_surjective
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (himm : ∀ z, Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F z)) :
    IsOpen {x | Function.Surjective (trueSecondForm F hF x)} := by
  have hset : {x | Function.Surjective (trueSecondForm F hF x)} =
      {x | N - Module.finrank ℝ E ≤ Module.finrank ℝ (trueSecondForm F hF x).range} := by
    ext x
    exact trueSecondForm_surjective_iff_finrank_ge F hF x (himm x)
  rw [hset]
  exact isOpen_trueSecondForm_finrank_ge F hF himm _

/-- The nonsupported full-rank region is genuinely open in the manifold,
obtained from the original relatively closed supported locus. -/
theorem isOpen_actual_fullRank_nonsupported
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (himm : ∀ z, Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F z))
    (hphase : PhaseRegular F hF) :
    IsOpen {x | Function.Surjective (trueSecondForm F hF x) ∧
      ¬ HasSupportedKernel (trueSecondForm F hF x)} := by
  have ho := (isOpen_trueSecondForm_surjective F hF himm).isOpenMap_subtype_val _
    (isClosed_actual_supported_in_fullRank F hF himm hphase).isOpen_compl
  convert ho using 1
  ext x
  simp only [mem_ofPred_eq, mem_image, mem_compl_iff]
  constructor
  · rintro ⟨hx, hnot⟩
    exact ⟨⟨x, hx⟩, hnot, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, hy⟩

/-- The current actual supported locus on a compact full-rank part of the
source is compact.  This allows it to be recomputed after each perturbation. -/
theorem isCompact_actual_supported_on_compact_fullRank
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (himm : ∀ z, Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F z))
    (hphase : PhaseRegular F hF) {C : Set M} (hC : IsCompact C)
    (hfull : ∀ x ∈ C, Function.Surjective (trueSecondForm F hF x)) :
    IsCompact {x ∈ C | HasSupportedKernel (trueSecondForm F hF x)} := by
  have hcompact := hC.diff (isOpen_actual_fullRank_nonsupported F hF himm hphase)
  convert hcompact using 1
  ext x
  simp only [mem_ofPred_eq, mem_sdiff]
  constructor
  · rintro ⟨hx, hs⟩
    exact ⟨hx, fun h ↦ h.2 hs⟩
  · rintro ⟨hx, hs⟩
    exact ⟨hx, by_contra fun h ↦ hs ⟨hfull x hx, h⟩⟩

/-- After removing supported kernels on a compact region (the n≥4 branch),
construct a compact-closure buffer of full-rank nonsupported points. -/
theorem exists_current_nonsupported_buffer
    [LocallyCompactSpace M] [RegularSpace M]
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (himm : ∀ z, Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F z))
    (hphase : PhaseRegular F hF) {C : Set M} (hC : IsCompact C)
    (hgood : ∀ x ∈ C, Function.Surjective (trueSecondForm F hF x) ∧
      ¬ HasSupportedKernel (trueSecondForm F hF x)) :
    ∃ W : Set M, IsOpen W ∧ C ⊆ W ∧ IsCompact (closure W) ∧
      ∀ x ∈ closure W, Function.Surjective (trueSecondForm F hF x) ∧
        ¬ HasSupportedKernel (trueSecondForm F hF x) := by
  obtain ⟨W, hW, hCW, hWgood, hWcompact⟩ :=
    exists_open_between_and_isCompact_closure hC
      (isOpen_actual_fullRank_nonsupported F hF himm hphase) hgood
  exact ⟨W, hW, hCW, hWcompact, hWgood⟩

/-- After supported-coincidence avoidance (in particular the n=3 branch),
protect the recomputed supported locus, then construct the remaining compact
full-rank nonsupported buffer.  The supported locus is allowed to be nonempty.
The pair gap protects either endpoint and therefore works across components. -/
theorem exists_current_supported_protected_complement
    [T2Space M] [LocallyCompactSpace M] [RegularSpace M]
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (himm : ∀ z, Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F z))
    (hphase : PhaseRegular F hF) {C : Set M} (hC : IsCompact C)
    (hfull : ∀ x ∈ C, Function.Surjective (trueSecondForm F hF x))
    {P : Set (M × M)} (hP : IsCompact P)
    (hsym : ∀ x y, (x, y) ∈ P → (y, x) ∈ P)
    (hseparated : ∀ z ∈ P, z.1 ∈ C →
      HasSupportedKernel (trueSecondForm F hF z.1) → F z.1 ≠ F z.2) :
    ∃ O W : Set M, IsOpen O ∧ IsOpen W ∧
      {x ∈ C | HasSupportedKernel (trueSecondForm F hF x)} ⊆ O ∧
      IsCompact (C \ O) ∧ C \ O ⊆ W ∧ IsCompact (closure W) ∧
      (∀ x ∈ closure W, Function.Surjective (trueSecondForm F hF x) ∧
        ¬ HasSupportedKernel (trueSecondForm F hF x)) ∧
      ∃ d > 0, ∀ z ∈ P, z.1 ∈ closure O ∨ z.2 ∈ closure O →
        d < ‖F z.1 - F z.2‖ := by
  let S := {x ∈ C | HasSupportedKernel (trueSecondForm F hF x)}
  have hS : IsCompact S :=
    isCompact_actual_supported_on_compact_fullRank F hF himm hphase hC hfull
  have hsep : ∀ z ∈ P, z.1 ∈ S ∨ z.2 ∈ S → F z.1 ≠ F z.2 := by
    intro z hz hbad
    rcases hbad with hx | hy
    · exact hseparated z hz hx.1 hx.2
    · exact (hseparated (z.2, z.1) (hsym z.1 z.2 hz) hy.1 hy.2).symm
  obtain ⟨O, hO, hSO, d, hd, hgap⟩ :=
    exists_protected_pair_neighborhood hP hS hF.continuous hsep
  have hD : IsCompact (C \ O) := hC.diff hO
  have hgood : ∀ x ∈ C \ O, Function.Surjective (trueSecondForm F hF x) ∧
      ¬ HasSupportedKernel (trueSecondForm F hF x) := by
    intro x hx
    exact ⟨hfull x hx.1, fun hs ↦ hx.2 (hSO ⟨hx.1, hs⟩)⟩
  obtain ⟨W, hW, hDW, hWcompact, hWgood⟩ :=
    exists_current_nonsupported_buffer F hF himm hphase hD hgood
  exact ⟨O, W, hO, hW, hSO, hD, hDW, hWcompact, hWgood, d, hd, hgap⟩

end GlobalEmbedding.Upgrade
