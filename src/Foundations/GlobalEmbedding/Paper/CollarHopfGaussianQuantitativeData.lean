import GlobalEmbedding.Paper.CollarHopfCompactAmbientExtension
import GlobalEmbedding.Paper.CollarHopfAmbientC5Neighborhood
import GlobalEmbedding.Paper.CollarHopfAmbientLittleMultiplierBound
import GlobalEmbedding.Paper.CollarHopfAmbientLittleForcingBound
import GlobalEmbedding.Paper.CollarHopfGaussianC5Choice

/-!
# Noncircular actual Gaussian quantitative data on the original Hopf product

Source: `main.tex`, prop:collar, lines520–526.
DAG: `collar-hopf-gaussian-quantitative-data`; sole AS2b owner W2.
This file ONLY combines accepted/frozen actual geometric/analytic inequalities.
The common multiplier constant is chosen BEFORE the forcing tolerance and F.
It does not assert Gaussian omega, an analytic seed, a fixed point or global glue.
-/

noncomputable section
open MeasureTheory Set
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- The FIXED original smooth free identity-Gram H0 supplies actual normalized
Gaussian approximants with a common ORIGINAL little multiplier bound and an
arbitrarily small ORIGINAL little raw OLD-Gram forcing, chosen noncircularly.

One compact extension f0 and common K are selected BEFORE the forcing tolerance,
ambient C5 tolerance, width cap, and approximating F. The latter is the ACTUAL
normalized Gaussian integral transported by the SAME original ambient CLE.
For every fixed nonnegative quadratic norm bound B, positive ball/forcing
thresholds also precede F and satisfy strict image, Lipschitz and small-solution
linearization inequalities. The arbitrary forcing tolerance can be that threshold.
All original native columns remain free; the actual matrix Gram is nonzero on
every original fiber. Coefficients and raw forcing have EXACT source lifts in
the same cofactor order, including the absence of a half in the raw forcing.

Proof: invoke the accepted compact extension, fixed C5 rank neighborhood,
original little multiplier bound and OLD-forcing bound. After their constants
are fixed, take a positive minimum with delta/(forcingConstant+1), then invoke
the actual Gaussian width choice once. Every conclusion follows by specializing
those same providers to the same F. No desired rank, norm or width is a premise.
This is quantitative AS2b data; native Gaussian omega and the actual69/glue/seed
construction remain separate obligations. Source: prop:collar520–526. -/
theorem collarHopf_gaussian_quantitative_data {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)]
    (H0 : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hH0 : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ H0)
    (hfree : ∀ x, LinearIndependent ℝ (freeFlowColumns (freeHopfProductFlow C) H0 x))
    (hmetric : ∀ x, Matrix.gram ℝ (fun i ↦ freeHopfDeriv C i H0 x) = 1) :
    let M := freeSymmetricColumnCount a + a
    ∃ (f0 : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N)) (K : ℝ),
      ContDiff ℝ ∞ f0 ∧ HasCompactSupport f0 ∧
      (∀ x, f0 (freeHopfAmbientInclusion C x) = H0 x) ∧ 0 < K ∧
      (∀ B : ℝ, 0 ≤ B → ∃ ρ ζ : ℝ, 0 < ρ ∧ 0 < ζ ∧
        2 * K * B * ρ < (1 / 2 : ℝ) ∧
        K * ζ / 2 + K * B * ρ ^ 2 < ρ ∧
        ∀ s : ℝ, 0 ≤ s → s < ζ → 4 * K * B * (K + 1) * s < (1 / 2 : ℝ)) ∧
      ∀ δ : ℝ, 0 < δ → ∀ τ : ℝ, 0 < τ → ∀ widthCap : ℝ, 0 < widthCap →
        ∃ (ε : ℝ) (F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N)),
          0 < ε ∧ ε < widthCap ∧
          (∀ p, F p = ∫ y : EuclideanSpace ℝ (Fin (CollarHopfAmbientDim C)),
            ((Real.pi * ε) ^ (-(CollarHopfAmbientDim C : ℝ) / 2) *
              Real.exp (-‖collarHopfAmbientCoordinates C p - y‖ ^ 2 / ε)) •
              f0 ((collarHopfAmbientCoordinates C).symm y)) ∧
          ContDiff ℝ ∞ F ∧
          (∀ p : FreeHopfAmbientSpace C, ∀ i ≤ 5,
            ‖iteratedFDeriv ℝ i (F - f0) p‖ ≤ τ) ∧
          (∀ x, LinearIndependent ℝ
            (freeFlowColumns (freeHopfProductFlow C) (F ∘ freeHopfAmbientInclusion C) x)) ∧
          (∀ x : FreeHopfProduct C, ∀ y : Fin a → ℝ,
            (collarAmbientHopfPairingMatrix C F
                (collarAmbientHopfAction C y (freeHopfAmbientInclusion C x)) *
              (collarAmbientHopfPairingMatrix C F
                (collarAmbientHopfAction C y (freeHopfAmbientInclusion C x))).transpose).det ≠ 0) ∧
          ∀ x : FreeHopfProduct C,
          ∃ (coeff : LittlePeriodicCAlphaFunction a (N * M) 2 (1 / 2 : ℝ))
            (h : LittlePeriodicCAlphaFunction a M 2 (1 / 2 : ℝ)),
            (∀ y : EuclideanSpace ℝ (Fin a), ∀ q : Fin (N * M),
              let T := collarAmbientHopfPairingMatrix C F
                (collarAmbientHopfAction C (fun i ↦ y i) (freeHopfAmbientInclusion C x))
              coeff.val.toFun y q = (T.transpose * (T * T.transpose)⁻¹)
                (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2) ∧
            ‖coeff‖ ≤ K ∧
            (∀ mult : LittlePeriodicCAlphaFunction a (N * M) 2 (1 / 2 : ℝ) →L[ℝ]
                LittlePeriodicCAlphaFunction a M 2 (1 / 2 : ℝ) →L[ℝ]
                  LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ),
              (∀ A u y, (mult A u).val.toFun y =
                hilbertSchmidtCoordinateEvaluation M N (A.val.toFun y) (u.val.toFun y)) →
              ‖mult coeff‖ ≤ K) ∧
            (∀ y : EuclideanSpace ℝ (Fin a), ∀ r : Fin M,
              h.val.toFun y r = match (freeCofactorColumnOrder a).symm r with
                | Sum.inl _ => 0
                | Sum.inr ij => collarAmbientHopfMetricDefect C F
                    (collarAmbientHopfAction C (fun i ↦ y i) (freeHopfAmbientInclusion C x))
                      ij.val.1 ij.val.2) ∧
            ‖h‖ < δ := by
  dsimp only
  obtain ⟨f0, hf0, hcompact, _, hsame, _⟩ := collarHopf_compact_ambient_extension C H0 hH0
  have hsamefun : f0 ∘ freeHopfAmbientInclusion C = H0 := funext hsame
  have hfree0 : ∀ x, LinearIndependent ℝ
      (freeFlowColumns (freeHopfProductFlow C) (f0 ∘ freeHopfAmbientInclusion C) x) := by
    rw [hsamefun]
    exact hfree
  have hmetric0 : ∀ x, Matrix.gram ℝ
      (fun i ↦ freeHopfDeriv C i (f0 ∘ freeHopfAmbientInclusion C) x) = 1 := by
    rw [hsamefun]
    exact hmetric
  obtain ⟨ηrank, μ, L, hηrank, _, _, hRank⟩ :=
    collarHopf_fixed_ambient_c5_neighborhood C f0 hf0 hfree0
  obtain ⟨ηmult, K, hηmult, hK, hMult⟩ :=
    collarHopf_fixed_ambient_c5_little_multiplier_bound C f0 hf0 hfree0
  obtain ⟨Cforce, hCforce, hForce⟩ :=
    collarHopf_ambient_c5_little_forcing_bound C f0 hf0 hcompact hmetric0
  refine ⟨f0, K, hf0, hcompact, hsame, hK, ?_, ?_⟩
  · intro B hB
    obtain ⟨ρ, hρ, hquad⟩ := exists_pos_mul_lt (by norm_num : (0 : ℝ) < 1 / 8) (K * B)
    obtain ⟨ζ0, hζ0, hstrict⟩ :=
      exists_pos_mul_lt (by norm_num : (0 : ℝ) < 1 / 2) (4 * K * B * (K + 1))
    let ζ := min ζ0 (ρ / (K + 1))
    have hζ : 0 < ζ := lt_min hζ0 (div_pos hρ (by positivity))
    have hζρ : ζ * (K + 1) ≤ ρ :=
      (le_div_iff₀ (by positivity : 0 < K + 1)).mp (min_le_right _ _)
    refine ⟨ρ, ζ, hρ, hζ, by nlinarith, ?_, ?_⟩
    · have he := mul_lt_mul_of_pos_right hquad hρ
      nlinarith
    · intro s _hs hsz
      have hsz0 : s ≤ ζ0 := hsz.le.trans (min_le_left _ _)
      exact (mul_le_mul_of_nonneg_left hsz0 (by positivity)).trans_lt hstrict
  intro δ hδ τ hτ widthCap hwidthCap
  let η := min ηrank ηmult
  let α := min τ (min η (min 1 (δ / (Cforce + 1))))
  have hα : 0 < α := by dsimp only [α, η]; positivity
  have hατ : α ≤ τ := min_le_left _ _
  have hαη : α ≤ η := (min_le_right _ _).trans (min_le_left _ _)
  have hαtail : α ≤ min 1 (δ / (Cforce + 1)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hα1 : α ≤ 1 := hαtail.trans (min_le_left _ _)
  have hαδ : α ≤ δ / (Cforce + 1) := hαtail.trans (min_le_right _ _)
  have hsmall : Cforce * α < δ := by
    have he := (le_div_iff₀ (by positivity : 0 < Cforce + 1)).mp hαδ
    nlinarith
  obtain ⟨ε, hε, hwidth, hF, herr⟩ :=
    collarHopf_gaussian_ambient_c5_choice C f0 hf0 hcompact α hα widthCap hwidthCap
  let d := CollarHopfAmbientDim C
  let G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin N) := fun p ↦
    ∫ y : EuclideanSpace ℝ (Fin d),
      ((Real.pi * ε) ^ (-(d : ℝ) / 2) * Real.exp (-‖p - y‖ ^ 2 / ε)) •
        f0 ((collarHopfAmbientCoordinates C).symm y)
  let F := G ∘ collarHopfAmbientCoordinates C
  have hF' : ContDiff ℝ ∞ F := hF
  have herror (z : FreeHopfProduct C) (i : ℕ) (hi : i ≤ 5) :
      ‖iteratedFDeriv ℝ i (F - f0) (freeHopfAmbientInclusion C z)‖ ≤ α :=
    herr _ i hi
  obtain ⟨hstable, _, hdet⟩ := hRank F hF'
    (fun z i hi ↦ (herror z i hi).trans (hαη.trans (min_le_left _ _)))
  refine ⟨ε, F, hε, hwidth, fun p ↦ rfl, hF',
    (fun p i hi ↦ (herr p i hi).trans hατ), fun z ↦ (hstable z).1, hdet, ?_⟩
  intro z
  obtain ⟨coeff, hcoeff, hcoeffNorm, hmult⟩ := hMult F hF'
    (fun z i hi ↦ (herror z i hi).trans (hαη.trans (min_le_right _ _))) z
  obtain ⟨h, hvalues, hbound⟩ := hForce F hF' α hα.le hα1 herror z
  exact ⟨coeff, h, hcoeff, hcoeffNorm, hmult, hvalues, hbound.trans_lt hsmall⟩

end GlobalEmbedding.Paper
