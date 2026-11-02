import GlobalEmbedding.Paper.FreeHopfProductRetraction
import GlobalEmbedding.Paper.CollarGaussianApproximation
import GlobalEmbedding.Paper.CollarAffineJetBound
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Actual compact ambient extension of a native smooth Hopf-product map

Source: `main.tex`, prop:collar proof, line520.
DAG: `collar-hopf-compact-ambient-extension`; exclusive owner W2.
Reuse Mathlib's compact-between and smooth neighborhood-cutoff theorems, together
with the existing actual radial retraction. The local-support extension argument
also appears in CalabiYau CompactSecant.exists_contDiff_compact_extension_of_contDiffOn;
here its genuine original Hopf data are supplied internally at infinite order.
-/

noncomputable section
open Set Filter Function MeasureTheory
open scoped Manifold ContDiff Topology

namespace GlobalEmbedding.Paper

/-- Every native smooth H on the actual whole Hopf product has an actual smooth
compactly supported extension on the SAME ambient normed space. The support is
inside its actual nonzero-factor domain, and on a neighborhood of the whole
product the extension is exactly the existing radial pullback of H. Thus the
actual inclusion values agree with H, without any given cutoff or extension.
Source: prop:collar, compact radial extension at line520. -/
theorem collarHopf_compact_ambient_extension {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)]
    (H : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hH : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ H) :
    ∃ f : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N),
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ freeHopfAmbientDomain C ∧
      (∀ x, f (freeHopfAmbientInclusion C x) = H x) ∧
      ∃ V : Set (FreeHopfAmbientSpace C), IsOpen V ∧
        Set.range (freeHopfAmbientInclusion C) ⊆ V ∧
        ∃ hVU : V ⊆ freeHopfAmbientDomain C,
          ∀ z (hz : z ∈ V),
            f z = H (freeHopfRadialRetraction C ⟨z, hVU hz⟩) := by
  classical
  let E := FreeHopfAmbientSpace C
  let U := freeHopfAmbientDomain C
  let K := Set.range (freeHopfAmbientInclusion C)
  have hK : IsCompact K := freeHopfAmbientInclusion_isCompact_range C
  have hKU : K ⊆ U := freeHopfAmbientInclusion_range_subset C
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK U.isOpen hKU
  obtain ⟨χ, hχone, hχzero, _⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (I := 𝓘(ℝ, E))
      (n := (⊤ : ℕ∞)) hK.isClosed hKL
  have hχ : ContDiff ℝ ∞ (χ : E → ℝ) := χ.contMDiff.contDiff
  have hχsupport : support (χ : E → ℝ) ⊆ L := by
    intro z hz
    by_contra hn
    exact hz (hχzero z hn)
  have hχtsupport : tsupport (χ : E → ℝ) ⊆ U :=
    (closure_minimal hχsupport hL.isClosed).trans hLU
  let raw : E → EuclideanSpace ℝ (Fin N) := fun z ↦
    if hz : z ∈ U then H (freeHopfRadialRetraction C ⟨z, hz⟩) else 0
  have hraw : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
      (fun z : U ↦ raw z) := by
    convert hH.comp (freeHopfRadialRetraction_contMDiff C) using 1
    funext z
    simp only [raw, dite_eq_left z.property, Function.comp_def]
    rfl
  have hrawAt (z : E) (hz : z ∈ U) : ContDiffAt ℝ ∞ raw z :=
    (contMDiffAt_subtype_iff.mp (hraw ⟨z, hz⟩)).contDiffAt
  let f : E → EuclideanSpace ℝ (Fin N) := fun z ↦ χ z • raw z
  have hf : ContDiff ℝ ∞ f := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ U
    · exact hχ.contDiffAt.smul (hrawAt z hz)
    · have hzero : (χ : E → ℝ) =ᶠ[𝓝 z] (fun _ ↦ 0) :=
        notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hz (hχtsupport h))
      apply (contDiffAt_const : ContDiffAt ℝ ∞
        (fun _ : E ↦ (0 : EuclideanSpace ℝ (Fin N))) z).congr_of_eventuallyEq
      filter_upwards [hzero] with y hy
      simp [f, hy]
  have hfsupport : support f ⊆ L := by
    intro z hz
    apply hχsupport
    intro hzero
    exact hz (by simp [f, hzero])
  have hfts : tsupport f ⊆ L := closure_minimal hfsupport hL.isClosed
  obtain ⟨V, hV, hKV, hVχ⟩ := eventually_nhdsSet_iff_exists.mp hχone
  have hVU : V ∩ (U : Set E) ⊆ U := inter_subset_right
  have hlocal (z : E) (hz : z ∈ V ∩ (U : Set E)) :
      f z = H (freeHopfRadialRetraction C ⟨z, hVU hz⟩) := by
    dsimp only [f]
    rw [hVχ z hz.1, one_smul]
    dsimp only [raw]
    exact dite_eq_left (show z ∈ U from hz.2)
  refine ⟨f, hf, HasCompactSupport.of_support_subset_isCompact hL hfsupport,
    hfts.trans hLU, ?_, V ∩ (U : Set E), hV.inter U.isOpen,
    fun z hz ↦ ⟨hKV hz, hKU hz⟩, hVU, hlocal⟩
  intro x
  rw [hlocal _ ⟨hKV (mem_range_self x), freeHopfAmbientInclusion_mem C x⟩]
  rw [freeHopfRadialRetraction_inclusion]

/-- The actual real dimension of the existing finite ambient space. Its original
finite-Pi maximum norm is retained. Source: prop:collar, line520. -/
abbrev CollarHopfAmbientDim {a : ℕ} (C : Fin a → ℕ) :=
  Module.finrank ℝ (FreeHopfAmbientSpace C)

/-- Genuine real continuous-linear coordinates for the SAME original ambient,
using Mathlib's finite-dimensional basis equivalence. This is not an isometry:
both actual operator norms are retained below. Source: prop:collar, line520. -/
def collarHopfAmbientCoordinates {a : ℕ} (C : Fin a → ℕ) :
    FreeHopfAmbientSpace C ≃L[ℝ] EuclideanSpace ℝ (Fin (CollarHopfAmbientDim C)) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp [CollarHopfAmbientDim])

/-- Pullback from actual Euclidean Gaussian parameters to the original ambient
retains precisely the actual coordinate-operator norm to the derivative order.
Reuse the accepted affine jet bound at zero shift. Source: prop:collar, line520. -/
theorem collarHopf_ambient_coordinate_jet_bound {a N : ℕ} (C : Fin a → ℕ)
    (f : EuclideanSpace ℝ (Fin (CollarHopfAmbientDim C)) → EuclideanSpace ℝ (Fin N))
    (hf : ContDiff ℝ ∞ f) (x : FreeHopfAmbientSpace C) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (f ∘ collarHopfAmbientCoordinates C) x‖ ≤
      ‖iteratedFDeriv ℝ j f (collarHopfAmbientCoordinates C x)‖ *
        ‖(collarHopfAmbientCoordinates C).toContinuousLinearMap‖ ^ j := by
  simpa only [zero_add, Function.comp_def, ContinuousLinearEquiv.coe_coe] using
    collar_affine_jet_bound f 0 (collarHopfAmbientCoordinates C).toContinuousLinearMap
      x j (by simpa only [zero_add] using (hf.of_le (by simp)).contDiffAt)

/-- Pushforward to the Euclidean Gaussian parameter coordinates retains the
actual inverse-operator norm to the derivative order. No equivalent norm is
silently treated as equal. Source: prop:collar, line520. -/
theorem collarHopf_euclidean_coordinate_jet_bound {a N : ℕ} (C : Fin a → ℕ)
    (f : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N))
    (hf : ContDiff ℝ ∞ f) (x : EuclideanSpace ℝ (Fin (CollarHopfAmbientDim C))) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (f ∘ (collarHopfAmbientCoordinates C).symm) x‖ ≤
      ‖iteratedFDeriv ℝ j f ((collarHopfAmbientCoordinates C).symm x)‖ *
        ‖(collarHopfAmbientCoordinates C).symm.toContinuousLinearMap‖ ^ j := by
  simpa only [zero_add, Function.comp_def, ContinuousLinearEquiv.coe_coe] using
    collar_affine_jet_bound f 0 (collarHopfAmbientCoordinates C).symm.toContinuousLinearMap
      x j (by simpa only [zero_add] using (hf.of_le (by simp)).contDiffAt)

/-- The actual compact radial extension of the original H supplies the FULL
accepted Gaussian theorem directly, in genuine real Euclidean coordinates:
entire complex extensions, exact real restrictions and the global every-Ck
limit for this same transported extension. The original ambient and target
norms are unchanged; coordinate jet bounds above retain both true operator
norms. No desired analytic exact metric or analytic seed is assumed.
Source: prop:collar, radial extension and Gaussian approximation at line520. -/
theorem collarHopf_compact_extension_gaussian {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)]
    (H : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hH : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ H) :
    ∃ f : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N),
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ freeHopfAmbientDomain C ∧
      (∀ x, f (freeHopfAmbientInclusion C x) = H x) ∧
      (∃ V : Set (FreeHopfAmbientSpace C), IsOpen V ∧
        Set.range (freeHopfAmbientInclusion C) ⊆ V ∧
        ∃ hVU : V ⊆ freeHopfAmbientDomain C,
          ∀ z (hz : z ∈ V),
            f z = H (freeHopfRadialRetraction C ⟨z, hVU hz⟩)) ∧
      let d := CollarHopfAmbientDim C
      let g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin N) :=
        f ∘ (collarHopfAmbientCoordinates C).symm
      let G : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin N) := fun ε x ↦
        ∫ y : EuclideanSpace ℝ (Fin d),
          ((Real.pi * ε) ^ (-(d : ℝ) / 2) * Real.exp (-‖x - y‖ ^ 2 / ε)) • g y
      let F : ℝ → EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin N) := fun ε z ↦
        ∫ y : Fin d → ℝ,
          ((((Real.pi * ε) ^ (-(d : ℝ) / 2) : ℝ) : ℂ) *
            Complex.exp (-(∑ i : Fin d, (z i - (y i : ℂ)) ^ 2) / (ε : ℂ))) •
              collarGaussianRealToComplex N (g (WithLp.toLp 2 y))
      (∀ ε : ℝ, 0 < ε → Differentiable ℂ (F ε) ∧
        (∀ x : EuclideanSpace ℝ (Fin d),
          F ε (collarGaussianRealToComplex d x) = collarGaussianRealToComplex N (G ε x)) ∧
        ContDiff ℝ ∞ (G ε)) ∧
      ∀ k : ℕ, Tendsto
        (fun ε : ℝ ↦ ⨆ n : Fin (k + 1), ⨆ x : EuclideanSpace ℝ (Fin d),
          ‖iteratedFDeriv ℝ n.val (G ε) x - iteratedFDeriv ℝ n.val g x‖)
        (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨f, hf, hcompact, hsupport, hsame, hlocal⟩ :=
    collarHopf_compact_ambient_extension C H hH
  refine ⟨f, hf, hcompact, hsupport, hsame, hlocal, ?_⟩
  let e := collarHopfAmbientCoordinates C
  have hg : ContDiff ℝ ∞ (f ∘ e.symm) := hf.comp e.symm.contDiff
  have hgcompact : HasCompactSupport (f ∘ e.symm) :=
    hcompact.comp_homeomorph e.symm.toHomeomorph
  exact collar_gaussian_approximation (f ∘ e.symm) hg hgcompact

end GlobalEmbedding.Paper
