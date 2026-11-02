import NormalPolar.NativeProbeTotalizationInitial
import GlobalEmbedding.Offline.UniformDiagonalSeparation

/-!
# Fixed reference budgets from the genuine compact atlas

Smoothness of the given reference map and compactness of the original
support sets imply finiteness of the original Cj norm at every order.
No reference norm budget is an input. The chosen real coefficient is fixed
before any scale, probe parameter, first increment, or repair run.
-/

noncomputable section
open Manifold Set GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff ENNReal

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ, E)

/-- The original atlas Cj norm of the true smooth reference is finite.
The coordinate norm uses exactly the original support sets. -/
theorem compact_reference_probeAtlasCj_ne_top
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀) (j : ℕ) :
    probeAtlasCj A j F₀ ≠ ⊤ := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  let v := EuclideanSpace.equiv (Fin N) ℝ
  let O := fun i ↦ e '' (A.chart i).target
  let S := fun i ↦ e '' ((A.chart i) '' A.support i)
  let f := fun i y ↦ v (F₀ ((A.chart i).symm (e.symm y)))
  have hO (i) : IsOpen (O i) := e.toHomeomorph.isOpenMap _ (A.chart i).open_target
  have hSO (i) : S i ⊆ O i := by
    rintro y ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨A.chart i x, (A.chart i).map_source (hA.support_subset i hx), rfl⟩
  have hS (i) : IsCompact (S i) :=
    ((hcompact i).image_of_continuousOn
      ((A.chart i).continuousOn.mono (hA.support_subset i))).image e.continuous
  exact paperAtlasCj_ne_top_of_compact j f O S hO hSO hS
    (fun i ↦ probeAtlas_coordinate_smooth A hA F₀ hF₀ i)

/-- Finiteness is proved before using the real projection of the norm. -/
theorem exists_compact_reference_probeAtlasCj_bound
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ probeAtlasCj A j F₀ ≤ ENNReal.ofReal C := by
  have hfinite := compact_reference_probeAtlasCj_ne_top A hA hcompact F₀ hF₀ j
  refine ⟨(probeAtlasCj A j F₀).toReal, ENNReal.toReal_nonneg, ?_⟩
  rw [ENNReal.ofReal_toReal hfinite]

/-- A reference coefficient chosen from the actual fixed atlas and map. -/
def compactReferenceCjConstant
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀) (j : ℕ) : ℝ :=
  Classical.choose (exists_compact_reference_probeAtlasCj_bound A hA hcompact F₀ hF₀ j)

theorem compactReferenceCjConstant_nonneg
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀) (j : ℕ) :
    0 ≤ compactReferenceCjConstant A hA hcompact F₀ hF₀ j :=
  (Classical.choose_spec (exists_compact_reference_probeAtlasCj_bound A hA hcompact F₀ hF₀ j)).1

theorem compactReferenceCjConstant_bound
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀) (j : ℕ) :
    probeAtlasCj A j F₀ ≤ ENNReal.ofReal (compactReferenceCjConstant A hA hcompact F₀ hF₀ j) :=
  (Classical.choose_spec (exists_compact_reference_probeAtlasCj_bound A hA hcompact F₀ hF₀ j)).2

/-- The three genuine initial-center terms are absorbed on the entire
fixed threshold interval. This is used after a concrete same-run tail proof. -/
theorem actualProbeCenterC1Constant_absorbs
    (threshold Cref Cinc Ctail s : ℝ)
    (hCref : 0 ≤ Cref) (hCtail : 0 ≤ Ctail)
    (hs : 0 < s) (hsT : s < threshold) :
    Cref * s ^ (20 : ℕ) + Cinc * s ^ (10 : ℕ) + Ctail * s ^ (12 : ℕ) ≤
      actualProbeCenterC1Constant threshold Cref Cinc Ctail * s ^ (10 : ℕ) := by
  have hsmax : s ≤ max 1 threshold := hsT.le.trans (le_max_right _ _)
  have h20 : s ^ (20 : ℕ) ≤ (max 1 threshold) ^ (10 : ℕ) * s ^ (10 : ℕ) := by
    calc
      s ^ (20 : ℕ) = s ^ (10 : ℕ) * s ^ (10 : ℕ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs.le hsmax 10)
        (pow_nonneg hs.le _)
  have h12 := pow_twelve_le_threshold_sq_mul_pow_ten threshold s hs hsT
  calc
    _ ≤ Cref * ((max 1 threshold) ^ (10 : ℕ) * s ^ (10 : ℕ)) + Cinc * s ^ (10 : ℕ) +
        Ctail * ((max 1 threshold) ^ (2 : ℕ) * s ^ (10 : ℕ)) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left h20 hCref) le_rfl)
        (mul_le_mul_of_nonneg_left h12 hCtail)
    _ = _ := by unfold actualProbeCenterC1Constant; ring

variable {F₀ : M → EuclideanSpace ℝ (Fin N)}
    {hF₀ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F₀}
    {A : BufferedAtlas M (EuclideanSpace ℝ (Fin n))} {hA : IsSmoothBufferedAtlas A}
    {hcompact : ∀ i, IsCompact (A.support i)}
    {hcover : ∀ x, ∃ i, x ∈ A.support i}
    {hi₀ : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F₀ x)}
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}

/-- The initial-map same-Q certificate, with the reference C1 budget
constructed from its actual smoothness and the original compact supports. -/
def NativeProbeDomainData.chosenNormalGapOfCompactActualInitial [T2Space M]
    (d : NativeProbeDomainData F₀ hF₀ A hA hcompact hcover hi₀ waves)
    (initial U₀ : ℝ → ProbeParameters r → M → V)
    (hidentity : ∀ t, 0 < t → t < d.threshold →
      initial t 0 = actualProbeFirstMap F₀ U₀ t 0)
    (Cinc Ctail : ℝ) (hCinc : 0 ≤ Cinc) (hCtail : 0 ≤ Ctail)
    (hU : ∀ t, 0 < t → t < d.threshold → ContMDiff IM 𝓘(ℝ, V) ∞ (U₀ t 0))
    (hinc : ∀ t, 0 < t → t < d.threshold →
      probeAtlasCj A 1 (U₀ t 0) ≤ ENNReal.ofReal (Cinc * t ^ (10 : ℕ)))
    (htail : ∀ t, 0 < t → t < d.threshold →
      probeAtlasCj A 1 (d.map t 0 - initial t 0) ≤
        ENNReal.ofReal (Ctail * t ^ (12 : ℕ))) :
    ChosenProbeNormalGap (n := n) (N := N) (M := M) d.toExactProbeFamily :=
  d.chosenNormalGapOfActualInitial initial U₀ hidentity
    (compactReferenceCjConstant A hA hcompact F₀ hF₀ 1) Cinc Ctail
    (compactReferenceCjConstant_nonneg A hA hcompact F₀ hF₀ 1) hCinc hCtail
    (compactReferenceCjConstant_bound A hA hcompact F₀ hF₀ 1) hU hinc htail

end GlobalEmbedding.NormalPolar
