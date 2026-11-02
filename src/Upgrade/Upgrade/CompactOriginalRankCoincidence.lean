import Upgrade.CompactFixedAtlasRank

/-!
# No new actual rank-coincidences outside the chosen cover

The only smallness input is the original fixed-atlas C² norm. Compactness of
the old value-coincidence set supplies a buffered high-rank region, while the
old nonzero values on its complement supply a uniform value reserve. The
argument applies to the actual later map at both endpoints and re-evaluates
its own true second form.
-/

noncomputable section
open Set Bundle Manifold Module GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.Upgrade

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
  [T2Space M] [LocallyCompactSpace M] [RegularSpace M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- Every actual low-rank coincidence of every sufficiently original-C²
nearby smooth map lies in the fixed old open cover. Empty bad sets, cross-
component pairs, and global probe tails are included without extra hypotheses. -/
theorem exists_originalC2_rankCoincidence_exclusion
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hcoverA : ∀ x, ∃ i, x ∈ A.support i) (hdim : 2 ≤ n)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hphase : PhaseRegular F hF) (q : ℕ)
    {P U : Set (M × M)} (hP : IsCompact P) (hU : IsOpen U)
    (hcover : ∀ z ∈ P, finrank ℝ (trueSecondForm F hF z.1).range ≤ q →
      F z.1 = F z.2 → z ∈ U) :
    ∃ e > 0, ∀ (G : M → V) (hG : ContMDiff IM 𝓘(ℝ, V) ∞ G),
      probeAtlasCj A 2 (G - F) ≤ ENNReal.ofReal e →
      ∀ z ∈ P, finrank ℝ (trueSecondForm G hG z.1).range ≤ q →
        G z.1 = G z.2 → z ∈ U := by
  let D := P \ U
  have hD : IsCompact D := hP.diff hU
  let K := {z ∈ D | F z.1 = F z.2}
  have hK : IsCompact K := hD.inter_right
    (isClosed_eq (hF.continuous.comp continuous_fst)
      (hF.continuous.comp continuous_snd))
  let S := Prod.fst '' K
  have hS : IsCompact S := hK.image continuous_fst
  let high := {x | q + 1 ≤ finrank ℝ (trueSecondForm F hF x).range}
  have hhigh : IsOpen high := isOpen_trueSecondForm_finrank_ge F hF himm (q + 1)
  have hShigh : S ⊆ high := by
    rintro x ⟨z, hz, rfl⟩
    change q + 1 ≤ finrank ℝ (trueSecondForm F hF z.1).range
    by_contra h
    exact hz.1.2 (hcover z hz.1.1 (by omega) hz.2)
  obtain ⟨W, hW, hSW, hWhigh, hWcompact⟩ :=
    exists_open_between_and_isCompact_closure hS hhigh hShigh
  have hWrank : ∀ x ∈ closure W, q < finrank ℝ (trueSecondForm F hF x).range := hWhigh
  obtain ⟨erank, herank, hrank⟩ := exists_originalC2_rank_reserve
    A hA hcompact hcoverA hdim F hF himm hphase q hWcompact hWrank
  let Φ : M × M → V := fun z ↦ F z.1 - F z.2
  have hΦ : Continuous Φ :=
    (hF.continuous.comp continuous_fst).sub (hF.continuous.comp continuous_snd)
  obtain ⟨d, hd, hvaluestable⟩ := compact_no_new_incidence (Φ := Φ) hD
    (hW.preimage continuous_fst) (isClosed_singleton : IsClosed ({0} : Set V))
    hΦ.continuousOn (by
      intro z hz hzero
      exact hSW ⟨z, ⟨hz, sub_eq_zero.mp (show Φ z = 0 from hzero)⟩, rfl⟩)
  let C := ‖(EuclideanSpace.equiv (Fin N) ℝ).symm.toContinuousLinearMap‖
  have hC : 0 ≤ C := norm_nonneg _
  let e := min erank (d / (4 * (1 + C)))
  have he : 0 < e := lt_min herank (div_pos hd (by positivity))
  have hCe : C * e ≤ d / 4 := by
    have hCe' : (1 + C) * e ≤ d / 4 := by
      have h := mul_le_mul_of_nonneg_left (min_le_right erank (d / (4 * (1 + C))))
        (by positivity : 0 ≤ 1 + C)
      have heq : (1 + C) * (d / (4 * (1 + C))) = d / 4 := by field_simp
      exact h.trans_eq heq
    exact (mul_le_mul_of_nonneg_right (by linarith : C ≤ 1 + C) he.le).trans hCe'
  refine ⟨e, he, ?_⟩
  intro G hG hbudget z hz hlow hsame
  by_contra hzout
  have hclose (x : M) : ‖G x - F x‖ ≤ d / 4 :=
    (norm_le_of_probeAtlasCj A hA hcoverA 2 (G - F) he.le hbudget x).trans hCe
  have hvalueclose : ∀ w ∈ D, dist (G w.1 - G w.2) (Φ w) < d := by
    intro w _
    rw [dist_eq_norm]
    change ‖(G w.1 - G w.2) - (F w.1 - F w.2)‖ < d
    have hid : (G w.1 - G w.2) - (F w.1 - F w.2) =
        (G w.1 - F w.1) - (G w.2 - F w.2) := by abel
    rw [hid]
    apply (norm_sub_le _ _).trans_lt
    have h1 := hclose w.1
    have h2 := hclose w.2
    linarith
  have hzW : z.1 ∈ W := hvaluestable (fun w ↦ G w.1 - G w.2)
    hvalueclose z ⟨hz, hzout⟩ (sub_eq_zero.mpr hsame)
  have hhighG := hrank G hG
    (hbudget.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _))) z.1 (subset_closure hzW)
  exact (not_le_of_gt hhighG) hlow

end GlobalEmbedding.Upgrade
