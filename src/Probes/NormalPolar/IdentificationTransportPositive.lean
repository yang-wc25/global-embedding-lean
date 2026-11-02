import NormalPolar.IdentificationTransportExact
import NormalPolar.IdentificationTransportCanonical
import NormalPolar.PositiveUniqueness

/-!
# Exact compatibility with a genuine positive compression presentation

An existing actual normal identification represented by a positive inverse
square root of the true normal compression is the same polar identification
on the admitted domain. Its original second-form response is therefore
transported by equality of the actual functions in a neighborhood, without
any new old-Q derivative budget. A same-Q gap for the original record can
also be constructed directly, without replacing its normal identification.
-/

noncomputable section
open Set Filter Manifold
open scoped Topology ContDiff ENNReal

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade GlobalEmbedding.Continuation

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- A genuine positive inverse-square-root presentation of an existing
actual Q. All operators use its real normal projections. No same-Q equality,
operator gap, or response conclusion is a field of this presentation. -/
structure PositiveProbeNormalPresentation
    {F₀ : M → V} {r : ℕ} (p : ProbeGeometry (n := n) F₀ r) where
  inverseSqrt : ∀ (t : ℝ) (u : ProbeParameters r) (z : M),
    normalSpace (I := IM) F₀ z →L[ℝ] normalSpace (I := IM) F₀ z
  positive : ∀ t, 0 < t → t < p.threshold → ∀ u, ‖u‖ < p.radius → ∀ z,
    (inverseSqrt t u z).IsPositive
  square : ∀ t, 0 < t → t < p.threshold → ∀ u, ‖u‖ < p.radius → ∀ z,
    inverseSqrt t u z * inverseSqrt t u z =
      (normalProjectionCompression (normalSpace (I := IM) F₀ z)
        (normalSpace (I := IM) (p.map t u) z).starProjection).inverse
  operator_formula : ∀ t, 0 < t → t < p.threshold → ∀ u, ‖u‖ < p.radius → ∀ z,
    normalIdentificationOperator (n := n) F₀ (p.map t u) (p.normalIdentification t u) z =
      (normalSpace (I := IM) F₀ z).subtypeL.comp
        ((inverseSqrt t u z).comp ((normalSpace (I := IM) F₀ z).orthogonalProjectionOnto.comp
          (normalSpace (I := IM) (p.map t u) z).starProjection))

/-- The positive presentation equals the explicit polar operator wherever
the actual two projections are transverse in the quantitative norm sense. -/
theorem PositiveProbeNormalPresentation.operator_eq_polar
    {F₀ : M → V} {r : ℕ} {p : ProbeGeometry (n := n) F₀ r}
    (presentation : PositiveProbeNormalPresentation p)
    (t : ℝ) (ht : 0 < t) (htt : t < p.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < p.radius) (z : M)
    (hclose : ‖(normalSpace (I := IM) F₀ z).starProjection -
      (normalSpace (I := IM) (p.map t u) z).starProjection‖ < 1) :
    normalIdentificationOperator (n := n) F₀ (p.map t u) (p.normalIdentification t u) z =
      actualPolarOperator (normalSpace (I := IM) F₀ z).starProjection
        (normalSpace (I := IM) (p.map t u) z).starProjection := by
  rw [presentation.operator_formula t ht htt u hu z]
  exact positive_compression_formula_eq_actualPolarOperator
    (normalSpace (I := IM) F₀ z) (normalSpace (I := IM) (p.map t u) z) hclose
    (presentation.inverseSqrt t u z) (presentation.positive t ht htt u hu z)
    (presentation.square t ht htt u hu z)

/-- No change of identification is needed to attach the same-Q gap to an
original probe with a positive presentation. The original C² budget supplies
the projection gap; the large-scale bound uses that very original Q. -/
def chosenProbeNormalGapOfPositivePresentation
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (p : ExactProbeFamily F₀ hF₀ A waves)
    (presentation : PositiveProbeNormalPresentation p.toProbeGeometry) :
    ChosenProbeNormalGap p := by
  apply chosenProbeNormalGapOfOriginalC2 hA hcompact hi₀ p
  intro t ht htt u hu i z hz hclose
  exact presentation.operator_eq_polar t ht htt u hu z (by simpa only [norm_sub_rev] using hclose)

/-- A positive presentation of the old actual Q forces equality with the
canonical Q on the entire original admitted domain. -/
theorem exactPositive_sameNormalOperatorOnProbeDomain
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (p : ExactProbeFamily F₀ hF₀ A waves)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (hreserve : ∀ t, 0 < t → t < p.threshold → ∀ u, ‖u‖ < p.radius → ∀ z,
      ‖(normalSpace (I := IM) F₀ z).starProjection -
        (normalSpace (I := IM) (p.map t u) z).starProjection‖ < 1)
    (presentation : PositiveProbeNormalPresentation p.toProbeGeometry) :
    SameNormalOperatorOnProbeDomain p.toProbeGeometry (canonicalNormalIdentificationOfProbe p hi₀) := by
  intro t ht htt u hu z
  have hcanonical := actualImmersionNormalIdentification_operator F₀ (p.map t u) hi₀
    (probeGeometry_all_slice_immersion p.toProbeGeometry hi₀ t u) z (hreserve t ht htt u hu z)
  exact hcanonical.trans (presentation.operator_eq_polar t ht htt u hu z (hreserve t ht htt u hu z)).symm

/-- The two actual fiber isometries themselves agree, not merely the
estimates of their ambient operators. -/
theorem exactPositive_normalIdentification_eq
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (p : ExactProbeFamily F₀ hF₀ A waves)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (hreserve : ∀ t, 0 < t → t < p.threshold → ∀ u, ‖u‖ < p.radius → ∀ z,
      ‖(normalSpace (I := IM) F₀ z).starProjection -
        (normalSpace (I := IM) (p.map t u) z).starProjection‖ < 1)
    (presentation : PositiveProbeNormalPresentation p.toProbeGeometry)
    (t : ℝ) (ht : 0 < t) (htt : t < p.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < p.radius) (z : M) :
    canonicalNormalIdentificationOfProbe p hi₀ t u z = p.normalIdentification t u z :=
  normalIdentification_eq_of_operator_eq F₀ (p.map t u)
    (canonicalNormalIdentificationOfProbe p hi₀ t u) (p.normalIdentification t u) z
    (exactPositive_sameNormalOperatorOnProbeDomain p hi₀ hreserve presentation t ht htt u hu z)

/-- A full canonical record from an equal positive presentation. The
second-form response is transported through the proved neighborhood equality
of native derivatives; no additional old-Q derivative budget is required. -/
def exactPositiveCanonicalProbe
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (p : ExactProbeFamily F₀ hF₀ A waves)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (hreserve : ∀ t, 0 < t → t < p.threshold → ∀ u, ‖u‖ < p.radius → ∀ z,
      ‖(normalSpace (I := IM) F₀ z).starProjection -
        (normalSpace (I := IM) (p.map t u) z).starProjection‖ < 1)
    (presentation : PositiveProbeNormalPresentation p.toProbeGeometry) :
    ExactProbeFamily F₀ hF₀ A waves :=
  exactProbeFamilyWithSameNormalOperator p (canonicalNormalIdentificationOfProbe p hi₀)
    (exactPositive_sameNormalOperatorOnProbeDomain p hi₀ hreserve presentation)

/-- All original quantitative data, including etaB, remain exactly the
same for the equal positive presentation on the original domain. -/
theorem exactPositiveCanonicalProbe_preserves
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (p : ExactProbeFamily F₀ hF₀ A waves)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (hreserve : ∀ t, 0 < t → t < p.threshold → ∀ u, ‖u‖ < p.radius → ∀ z,
      ‖(normalSpace (I := IM) F₀ z).starProjection -
        (normalSpace (I := IM) (p.map t u) z).starProjection‖ < 1)
    (presentation : PositiveProbeNormalPresentation p.toProbeGeometry) :
    let pnew := exactPositiveCanonicalProbe p hi₀ hreserve presentation
    pnew.map = p.map ∧ pnew.radius = p.radius ∧ pnew.threshold = p.threshold ∧
      pnew.weight = p.weight ∧ pnew.constant = p.constant ∧ pnew.etaB = p.etaB ∧
      pnew.etaV = p.etaV ∧ pnew.normalIdentification = canonicalNormalIdentificationOfProbe p hi₀ := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The original same-Q gap interface for the exact canonical presentation.
The gap is derived from C² for this very record, after the response has been
transported by actual local equality. -/
def chosenProbeNormalGapOfExactPositiveCanonical
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (p : ExactProbeFamily F₀ hF₀ A waves)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (hreserve : ∀ t, 0 < t → t < p.threshold → ∀ u, ‖u‖ < p.radius → ∀ z,
      ‖(normalSpace (I := IM) F₀ z).starProjection -
        (normalSpace (I := IM) (p.map t u) z).starProjection‖ < 1)
    (presentation : PositiveProbeNormalPresentation p.toProbeGeometry) :
    ChosenProbeNormalGap (exactPositiveCanonicalProbe p hi₀ hreserve presentation) := by
  apply chosenProbeNormalGapOfTotalCanonical hA hcompact hi₀
  intro t ht htt u hu
  rfl

end GlobalEmbedding.NormalPolar
