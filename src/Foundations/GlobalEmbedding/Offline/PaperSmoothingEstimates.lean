import GlobalEmbedding.Offline.LocalSmoothingEstimates
import GlobalEmbedding.Paper.PaperCoordinateNormBridge

/-!
# Local smoothing in the original cumulative coordinate norms

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines 700–719,
equation (6.4). This file reuses the frozen paper coordinate-partial
norms and their proved Fréchet comparison. The output is the actual
same local convolution error, not a separate sequence of jet objects.
The atlas norm is a maximum; no count of charts occurs in the constants.
-/

open MeasureTheory GlobalEmbedding.Paper
open scoped BigOperators ContDiff ENNReal

namespace GlobalEmbedding.Offline

noncomputable section

/-- The fixed finite-dimensional comparison factor already appearing
in the original coordinate/Fréchet norm bridge. -/
def coordinateDimensionFactor (d j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (j + 1), (d : ℝ) ^ k

/-- The comparison factor is nonnegative in every dimension and order. -/
theorem coordinateDimensionFactor_nonneg (d j : ℕ) :
    0 ≤ coordinateDimensionFactor d j :=
  Finset.sum_nonneg fun _ _ => pow_nonneg (Nat.cast_nonneg _) _

/-- Increasing the derivative order only increases the finite
comparison factor; this introduces no atlas-cardinality factor. -/
theorem coordinateDimensionFactor_mono (d : ℕ) {a b : ℕ} (hab : a ≤ b) :
    coordinateDimensionFactor d a ≤ coordinateDimensionFactor d b := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (Nat.add_le_add_right hab 1)
  · intro k _ _
    exact pow_nonneg (Nat.cast_nonneg _) _

/-- A uniform bound on all actual jets through j bounds the original
cumulative coordinate Cj maximum, directly through its exact native
coefficient identification. -/
theorem paperAtlasCj_le_of_jet_bound {ι : Type*} [Fintype ι] {d q : ℕ}
    (j : ℕ) (f : ι → (Fin d → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin d → ℝ)) (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i)) (B : ℝ)
    (hB : ∀ i, ∀ k ≤ j, ∀ x ∈ S i, ‖iteratedFDeriv ℝ k (f i) x‖ ≤ B) :
    paperAtlasCj j f O S ≤ ENNReal.ofReal B := by
  refine iSup_le fun i => ?_
  rw [paperCoordinateCj_eq_coordinateJetGauge j (f i) (O i) (S i) (hO i) (hSO i) (hf i)]
  refine iSup_le fun k => iSup_le fun x => iSup_le fun σ => iSup_le fun c => ?_
  exact ENNReal.ofReal_le_ofReal ((coordinate_jet_coefficient_le (f i) x σ c).trans
    (hB i k.val (by omega) x x.property))

/-- Finiteness of the original atlas Cj norm gives actual derivative
bounds on every chart, with exactly the existing dimension/order
comparison factor. -/
theorem paperAtlasCj_jet_le {ι : Type*} [Fintype ι] {d q : ℕ}
    (j : ℕ) (f : ι → (Fin d → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin d → ℝ)) (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i)) (hfinite : paperAtlasCj j f O S ≠ ⊤)
    (i : ι) {k : ℕ} (hk : k ≤ j) {x : Fin d → ℝ} (hx : x ∈ S i) :
    ‖iteratedFDeriv ℝ k (f i) x‖ ≤
      coordinateDimensionFactor d j * (paperAtlasCj j f O S).toReal := by
  have hbdd := (paperAtlasCj_ne_top_iff j f O S hO hSO hf).mp hfinite
  exact ((finiteCjNorm_specification j (f i) (S i) (hbdd i)).2.1 k hk x hx).trans
    (paperAtlasCj_finiteCjNorm_bound j f O S hO hSO hf hfinite i)

/-- Negation preserves the original cumulative atlas coordinate norm.
The proof uses native actual jet negation under the already proved
literal-coordinate-partial identification. -/
theorem paperAtlasCj_neg {ι : Type*} [Fintype ι] {d q : ℕ}
    (j : ℕ) (f : ι → (Fin d → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin d → ℝ)) (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i)) :
    paperAtlasCj j (fun i => -f i) O S = paperAtlasCj j f O S := by
  rw [paperAtlasCj_eq_coordinateAtlasJetGauge j (fun i => -f i) O S hO hSO (fun i => (hf i).neg),
    paperAtlasCj_eq_coordinateAtlasJetGauge j f O S hO hSO hf]
  simp only [coordinateAtlasJetGauge, coordinateJetGauge, iteratedFDeriv_neg_apply,
    neg_apply, Pi.neg_apply, norm_neg]

/-- The original weighted atlas norm is symmetric under reversing the
actual difference. This justifies either orientation of the smoothing
error without changing the original norm or relying on real infinity
totalization. -/
theorem paperAtlasWeighted_sub_comm {ι : Type*} [Fintype ι] {d q : ℕ}
    (base j : ℕ) (ell : ℝ) (f g : ι → (Fin d → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin d → ℝ)) (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i)) (hg : ∀ i, ContDiffOn ℝ ∞ (g i) (O i)) :
    paperAtlasWeighted base j ell (fun i x => f i x - g i x) O S =
      paperAtlasWeighted base j ell (fun i x => g i x - f i x) O S := by
  unfold paperAtlasWeighted
  apply Finset.sum_congr rfl
  intro a ha
  have h := paperAtlasCj_neg (a + base) (fun i x => f i x - g i x) O S hO hSO
    (fun i => (hf i).sub (hg i))
  have heq : (fun i => -(fun x => f i x - g i x)) = (fun i x => g i x - f i x) := by
    funext i x
    exact neg_sub _ _
  rw [heq] at h
  rw [h]

variable {d q : ℕ} (mu : Measure (Fin d → ℝ)) [mu.IsAddHaarMeasure]

/-- High-order estimate for the original cumulative coordinate norm of
the actual atlas family of local smoothing errors. Finiteness of the
output is part of the conclusion, before taking its real value. -/
theorem paperAtlasCj_smoothing_error_high_le {ι : Type*} [Fintype ι]
    {K : (Fin d → ℝ) → ℝ} (hK : ContDiff ℝ ∞ K) (hKcompact : HasCompactSupport K)
    (u : ι → (Fin d → ℝ) → Fin q → ℝ) (U V : ι → Set (Fin d → ℝ))
    (hU : ∀ i, IsOpen (U i)) (hV : ∀ i, IsOpen (V i)) (hUV : ∀ i, U i ⊆ V i)
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) (V i)) (ell : ℝ)
    (hbuffer : ∀ i, ∀ x ∈ U i, ∀ y ∈ tsupport K, x - ell • y ∈ V i)
    (j : ℕ) (hfinite : paperAtlasCj j u V V ≠ ⊤) :
    let e := fun i x => signedSmoothing mu K ell (u i) x - u i x
    paperAtlasCj j e U U ≠ ⊤ ∧
      (paperAtlasCj j e U U).toReal ≤
        ((1 + ∫ y, |K y| ∂mu) * coordinateDimensionFactor d j) *
          (paperAtlasCj j u V V).toReal := by
  dsimp only
  let e := fun i x => signedSmoothing mu K ell (u i) x - u i x
  let B := coordinateDimensionFactor d j * (paperAtlasCj j u V V).toReal
  let R := (1 + ∫ y, |K y| ∂mu) * B
  have hR : 0 ≤ R := mul_nonneg
    (add_nonneg zero_le_one (integral_nonneg fun y => abs_nonneg (K y)))
    (mul_nonneg (coordinateDimensionFactor_nonneg d j) ENNReal.toReal_nonneg)
  have he : ∀ i, ContDiffOn ℝ ∞ (e i) (U i) := by
    intro i
    exact (signedSmoothing_contDiffOn mu hK hKcompact (hU i) (hV i) (hu i) ell
      (hbuffer i)).sub ((hu i).mono (hUV i))
  have hbound : ∀ i, ∀ k ≤ j, ∀ x ∈ U i, ‖iteratedFDeriv ℝ k (e i) x‖ ≤ R := by
    intro i k hk x hx
    exact signedSmoothing_derivative_error_le_L1 mu hK hKcompact (hU i) (hV i)
      (hUV i) (hu i) ell (hbuffer i) k hx B (fun z hz =>
        paperAtlasCj_jet_le j u V V hV (fun _ => Set.Subset.rfl) hu hfinite i hk hz)
  have hle := paperAtlasCj_le_of_jet_bound j e U U hU (fun _ => Set.Subset.rfl) he R hbound
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  refine ⟨hfin, ?_⟩
  have hreal := (ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).mpr hle
  rw [ENNReal.toReal_ofReal hR] at hreal
  simpa only [R, B, mul_assoc] using hreal

/-- Low-order Taylor estimate for the original cumulative coordinate
Cj maximum, including j=r. The bound ell≤1 is precisely what allows
every lower-order jet in Cj to use the common factor ell^(r-j). -/
theorem paperAtlasCj_smoothing_error_low_le {ι : Type*} [Fintype ι]
    {kappa : (Fin d → ℝ) → ℝ} (hsmooth : ContDiff ℝ ∞ kappa)
    (hcompact : HasCompactSupport kappa) (hmass : (∫ y, kappa y ∂mu) = 1) (r : ℕ)
    (u : ι → (Fin d → ℝ) → Fin q → ℝ) (U V : ι → Set (Fin d → ℝ))
    (hU : ∀ i, IsOpen (U i)) (hV : ∀ i, IsOpen (V i)) (hUV : ∀ i, U i ⊆ V i)
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) (V i)) {ell : ℝ} (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (hsegments : ∀ i, ∀ x ∈ U i, ∀ y ∈ tsupport (finiteMomentKernel r kappa),
      ∀ t ∈ Set.Icc (0 : ℝ) 1, x - t • (ell • y) ∈ V i)
    (j : ℕ) (hjr : j ≤ r) (hfinite : paperAtlasCj r u V V ≠ ⊤) :
    let K := finiteMomentKernel r kappa
    let e := fun i x => signedSmoothing mu K ell (u i) x - u i x
    paperAtlasCj j e U U ≠ ⊤ ∧
      (paperAtlasCj j e U U).toReal ≤
        (kernelTailConstant mu K r * coordinateDimensionFactor d r) *
          ell ^ (r - j) * (paperAtlasCj r u V V).toReal := by
  dsimp only
  let K := finiteMomentKernel r kappa
  let e := fun i x => signedSmoothing mu K ell (u i) x - u i x
  let B := coordinateDimensionFactor d r * (paperAtlasCj r u V V).toReal
  let R := kernelTailConstant mu K r * B * ell ^ (r - j)
  have hB0 : 0 ≤ B := mul_nonneg (coordinateDimensionFactor_nonneg d r) ENNReal.toReal_nonneg
  have hR : 0 ≤ R := mul_nonneg
    (mul_nonneg (kernelTailConstant_nonneg mu K r) hB0) (pow_nonneg hell _)
  have hbuffer : ∀ i, ∀ x ∈ U i, ∀ y ∈ tsupport K, x - ell • y ∈ V i := by
    intro i x hx y hy
    simpa only [one_smul] using hsegments i x hx y hy 1 (by simp)
  have he : ∀ i, ContDiffOn ℝ ∞ (e i) (U i) := by
    intro i
    exact (signedSmoothing_contDiffOn mu (finiteMomentKernel_contDiff hsmooth r)
      (finiteMomentKernel_hasCompactSupport hcompact r) (hU i) (hV i) (hu i) ell
      (hbuffer i)).sub ((hu i).mono (hUV i))
  have hbound : ∀ i, ∀ k ≤ j, ∀ x ∈ U i, ‖iteratedFDeriv ℝ k (e i) x‖ ≤ R := by
    intro i k hk x hx
    have h := signedSmoothing_low_derivative_error_le mu hsmooth hcompact hmass r
      (hU i) (hV i) (hUV i) (hu i) hell (hsegments i) B hB0
      (fun a ha z hz => paperAtlasCj_jet_le r u V V hV (fun _ => Set.Subset.rfl)
        hu hfinite i ha hz) (hk.trans hjr) hx
    exact h.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one hell hell1 (Nat.sub_le_sub_left hk r))
      (mul_nonneg (kernelTailConstant_nonneg mu K r) hB0))
  have hle := paperAtlasCj_le_of_jet_bound j e U U hU (fun _ => Set.Subset.rfl) he R hbound
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  refine ⟨hfin, ?_⟩
  have hreal := (ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).mpr hle
  rw [ENNReal.toReal_ofReal hR] at hreal
  convert hreal using 1
  dsimp [R, B]
  ring

end

end GlobalEmbedding.Offline
