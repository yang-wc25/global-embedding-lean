import Upgrade.CompactProbeAtlas
import Upgrade.CompactBadSet

/-!
# Original C² exclusion of newly created value coincidences outside the cover

The old set is the actual current coincidence set on a compact pair region.
The later map may have a global correction tail. Both endpoint errors are
bounded in the literal original atlas norm; no support of the correction or
prior no-new-coincidences assertion is assumed.
-/

noncomputable section
open Set Bundle Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade
variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

theorem exists_originalC2_valueCoincidence_exclusion
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcoverA : ∀ x, ∃ i, x ∈ A.support i)
    (F : M → V) (hF : Continuous F)
    {P U : Set (M × M)} (hP : IsCompact P) (hU : IsOpen U)
    (hcover : ∀ z ∈ P, F z.1 = F z.2 → z ∈ U) :
    ∃ e > 0, ∀ G : M → V,
      probeAtlasCj A 2 (G - F) ≤ ENNReal.ofReal e →
      ∀ z ∈ P, G z.1 = G z.2 → z ∈ U := by
  let Phi : M × M → V := fun z ↦ F z.1 - F z.2
  have hPhi : Continuous Phi := (hF.comp continuous_fst).sub (hF.comp continuous_snd)
  obtain ⟨d, hd, hstable⟩ := compact_no_new_incidence hP hU
    (isClosed_singleton : IsClosed ({0} : Set V)) hPhi.continuousOn
    (fun z hz hzero ↦ hcover z hz (sub_eq_zero.mp (show Phi z = 0 from hzero)))
  let C := ‖(EuclideanSpace.equiv (Fin N) ℝ).symm.toContinuousLinearMap‖
  have hC : 0 ≤ C := norm_nonneg _
  let e := d / (4 * (1 + C))
  have he : 0 < e := div_pos hd (by positivity)
  have hCe : C * e ≤ d / 4 := by
    have heq : (1 + C) * e = d / 4 := by
      dsimp only [e]
      field_simp
    nlinarith [he.le]
  refine ⟨e, he, ?_⟩
  intro G hbudget
  have hclose (x : M) : ‖G x - F x‖ ≤ d / 4 :=
    (norm_le_of_probeAtlasCj A hA hcoverA 2 (G - F) he.le hbudget x).trans hCe
  have hpair : ∀ z ∈ P, dist (G z.1 - G z.2) (Phi z) < d := by
    intro z _
    rw [dist_eq_norm]
    change ‖(G z.1 - G z.2) - (F z.1 - F z.2)‖ < d
    have hid : (G z.1 - G z.2) - (F z.1 - F z.2) =
        (G z.1 - F z.1) - (G z.2 - F z.2) := by abel
    rw [hid]
    apply (norm_sub_le _ _).trans_lt
    linarith [hclose z.1, hclose z.2]
  intro z hz heq
  exact hstable (fun z ↦ G z.1 - G z.2) hpair z hz (sub_eq_zero.mpr heq)

end GlobalEmbedding.Upgrade
