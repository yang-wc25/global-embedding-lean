import Upgrade.CompactFixedAtlasSupported

/-!
# Original C² exclusion of newly created supported incidences

The source operation and the joint coincidence operation are distinct. The
second theorem permits surviving supported kernels and only confines their
actual coincidences; this is the case required in dimension three. All old
sets are formed from the current true form and current values, and all new
sets are evaluated on the later true form and later values.
-/

noncomputable section
open Set Bundle Manifold Module GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.Upgrade

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M] [T2Space M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The old supported bad-set cover remains a cover for every later smooth
map inside one original C² ball. This is a protection statement, not an
assertion that all supported kernels can be eliminated in dimension three. -/
theorem exists_originalC2_supported_exclusion
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hcoverA : ∀ x, ∃ i, x ∈ A.support i) (hdim : 2 ≤ n)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hphase : PhaseRegular F hF) {C U : Set M} (hC : IsCompact C) (hU : IsOpen U)
    (hfull : ∀ x ∈ C, Function.Surjective (trueSecondForm F hF x))
    (hcover : ∀ x ∈ C, HasSupportedKernel (trueSecondForm F hF x) → x ∈ U) :
    ∃ e > 0, ∀ (G : M → V) (hG : ContMDiff IM 𝓘(ℝ, V) ∞ G),
      probeAtlasCj A 2 (G - F) ≤ ENNReal.ofReal e →
      (∀ x ∈ C \ U, Function.Surjective (trueSecondForm G hG x)) ∧
        (∀ x ∈ C, HasSupportedKernel (trueSecondForm G hG x) → x ∈ U) := by
  obtain ⟨e, he, hstable⟩ := exists_originalC2_nonsupported_reserve
    A hA hcompact hcoverA hdim F hF himm hphase (hC.diff hU)
    (fun x hx ↦ ⟨hfull x hx.1, fun hs ↦ hx.2 (hcover x hx.1 hs)⟩)
  refine ⟨e, he, ?_⟩
  intro G hG hbudget
  constructor
  · intro x hx
    exact (hstable G hG hbudget x hx).1
  · intro x hx hs
    by_contra hxout
    exact (hstable G hG hbudget x ⟨hx, hxout⟩).2 hs

/-- In particular for n=3, a fixed open cover of current supported
coincidences captures every new supported coincidence for every sufficiently
original-C² nearby smooth map. Surviving supported kernels outside that
coincidence set are allowed. Both endpoint value errors are retained. -/
theorem exists_originalC2_supportedCoincidence_exclusion
    [LocallyCompactSpace M] [RegularSpace M]
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hcoverA : ∀ x, ∃ i, x ∈ A.support i) (hdim : 2 ≤ n)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hphase : PhaseRegular F hF)
    {P U : Set (M × M)} (hP : IsCompact P) (hU : IsOpen U)
    (hfull : ∀ z ∈ P, Function.Surjective (trueSecondForm F hF z.1))
    (hcover : ∀ z ∈ P, HasSupportedKernel (trueSecondForm F hF z.1) →
      F z.1 = F z.2 → z ∈ U) :
    ∃ e > 0, ∀ (G : M → V) (hG : ContMDiff IM 𝓘(ℝ, V) ∞ G),
      probeAtlasCj A 2 (G - F) ≤ ENNReal.ofReal e →
      ∀ z ∈ P, HasSupportedKernel (trueSecondForm G hG z.1) →
        G z.1 = G z.2 → z ∈ U := by
  let D := P \ U
  have hD : IsCompact D := hP.diff hU
  let K := {z ∈ D | F z.1 = F z.2}
  have hK : IsCompact K := hD.inter_right
    (isClosed_eq (hF.continuous.comp continuous_fst)
      (hF.continuous.comp continuous_snd))
  let S := Prod.fst '' K
  have hS : IsCompact S := hK.image continuous_fst
  have hSgood : ∀ x ∈ S, Function.Surjective (trueSecondForm F hF x) ∧
      ¬ HasSupportedKernel (trueSecondForm F hF x) := by
    rintro x ⟨z, hz, rfl⟩
    exact ⟨hfull z hz.1.1, fun hs ↦ hz.1.2 (hcover z hz.1.1 hs hz.2)⟩
  obtain ⟨W, hW, hSW, hWcompact, hWgood⟩ :=
    exists_current_nonsupported_buffer F hF himm hphase hS hSgood
  obtain ⟨eform, heform, hform⟩ := exists_originalC2_nonsupported_reserve
    A hA hcompact hcoverA hdim F hF himm hphase hWcompact hWgood
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
  let e := min eform (d / (4 * (1 + C)))
  have he : 0 < e := lt_min heform (div_pos hd (by positivity))
  have hCe : C * e ≤ d / 4 := by
    have hCe' : (1 + C) * e ≤ d / 4 := by
      have h := mul_le_mul_of_nonneg_left (min_le_right eform (d / (4 * (1 + C))))
        (by positivity : 0 ≤ 1 + C)
      have heq : (1 + C) * (d / (4 * (1 + C))) = d / 4 := by field_simp
      exact h.trans_eq heq
    exact (mul_le_mul_of_nonneg_right (by linarith : C ≤ 1 + C) he.le).trans hCe'
  refine ⟨e, he, ?_⟩
  intro G hG hbudget z hz hs hsame
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
  exact (hform G hG (hbudget.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _)))
    z.1 (subset_closure hzW)).2 hs

end GlobalEmbedding.Upgrade
