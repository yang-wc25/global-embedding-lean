import GlobalEmbedding.Paper.FreeCompactPivotPerturbation
import GlobalEmbedding.Paper.IncrementsModeAmbientTransverseFrame

/-!
# Finite conditioning witnesses for the SAME chosen transverse frame

Source: main.tex590–675 and697–701; original increments selected-phase gate5.
The accepted compact frame lower bound is reused, not reproved. All columns and
J below are the SOLE canonical actual W2 providers. Original compactness and the
original Good-to-frame caller must still be derived before using this in the
full target. No BEST-phase bound or desired inverse estimate is assumed.
-/

noncomputable section
open Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

variable {E H M Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [TopologicalSpace Q] {m N : ℕ}

local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}

/-- Qualitative injection of the SAME actual chosen columns on a genuine compact
set is equivalent to the EXISTENCE of a positive common squared lower bound.
The actual family may include all original finite parameters. The forward proof
is exactly the accepted compact-frame provider on the native compact subtype;
the converse evaluates the bound on a kernel vector. No numerical lower bound
is supplied as an original input. Source: finite chosen-phase conditioning. -/
theorem increments_chosen_transverse_compact_coercivity_iff
    (F : Q → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p)) (c : Q → D → M)
    (K : Set (Q × D)) (hK : IsCompact K)
    (hA : ContinuousOn
      (fun z : Q × D ↦ incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (c z.1) z.2) K) :
    (∀ z ∈ K, Function.Injective
      (incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (c z.1) z.2)) ↔
      ∃ lam : ℝ, 0 < lam ∧ ∀ z ∈ K, ∀ v : Tdata,
        lam * ‖v‖ ^ 2 ≤
          ‖incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (c z.1) z.2 v‖ ^ 2 := by
  let A := fun z : Q × D ↦
    incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (c z.1) z.2
  change (∀ z ∈ K, Function.Injective (A z)) ↔
    ∃ lam : ℝ, 0 < lam ∧ ∀ z ∈ K, ∀ v : Tdata, lam * ‖v‖ ^ 2 ≤ ‖A z v‖ ^ 2
  constructor
  · intro hinj
    let : CompactSpace K := isCompact_iff_compactSpace.mp hK
    have hc : Continuous (fun z : K ↦ A z) :=
      (show ContinuousOn A K from hA).domRestrict
    obtain ⟨lam, hlam, hb⟩ := free_compact_frame_lower_bound
      (fun z : K ↦ A z) hc (fun z ↦ hinj z z.property)
    exact ⟨lam, hlam, fun z hz v ↦ hb ⟨z, hz⟩ v⟩
  · rintro ⟨lam, hlam, hb⟩ z hz
    apply (injective_iff_map_eq_zero (A z)).2
    intro v hv
    by_contra hv0
    have hp : 0 < lam * ‖v‖ ^ 2 := mul_pos hlam (sq_pos_of_pos (norm_pos_iff.mpr hv0))
    exact (not_le_of_gt hp) (by simpa [hv] using hb z hz v)

/-- The SAME included canonical J has a finite bound on the ORIGINAL compact
set, derived from qualitative actual-frame injection and actual smoothness.
It is not a supplied inverse estimate. Reuse actual Gram smoothness and native
compactness, then rewrite ONLY with the canonical ambient-J identity.
Source: finite chosen-phase conditioning in the original increments construction. -/
theorem increments_chosen_transverse_compact_J_bound
    {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [TopologicalSpace Z] {J : ModelWithCorners ℝ Y Z} [ChartedSpace Z Q]
    (F : Q → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p)) (c : Q → D → M)
    (K : Set (Q × D)) (hK : IsCompact K)
    (hA : ContMDiffOn (J.prod 𝓘(ℝ, D)) 𝓘(ℝ, Tdata →L[ℝ] V) ∞
      (fun z : Q × D ↦ incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (c z.1) z.2) K)
    (hinj : ∀ z ∈ K, Function.Injective
      (incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (c z.1) z.2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ K,
      ‖(normalSpace (I := I) (F z.1) (c z.1 z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (c z.1) z.2)‖ ≤ C := by
  let A := fun z : Q × D ↦
    incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (c z.1) z.2
  have hR := freeGramRightInverse_contMDiffOn A hA hinj
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hR.continuousOn
  refine ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro z hz
  rw [incrementsModeCoordinateJ_ambient]
  exact (hC z hz).trans (le_max_right _ _)

end GlobalEmbedding.Paper
