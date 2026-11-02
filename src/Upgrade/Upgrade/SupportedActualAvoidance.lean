import Upgrade.SupportedActualProbeCoordinate
import Upgrade.SupportedProbePackets
import Upgrade.SupportedEquationStability
import GlobalEmbedding.Paper.AvoidanceEuclideanLocalNull

/-!
# Actual supported-kernel local avoidance in dimension n ≥ 4

The incidence map here is defined from the actual new slices, their actual
normal identification, and the actual normalized atlas inverse frames. The
selected directions are the actual q legal waves constructed from the strong
supported-rank theorem. Paired response errors imply the incidence rank;
that rank is never an input. The accepted avoidance theorem then makes the
projection of the ORIGINAL supported-kernel incidence locally null.

This is an explicit downstream theorem conditional on the full probe data:
joint smoothness of these actual coordinates, closeness to the old actual
form, and the stated full differentiated remainder bounds. It constructs no
probes and is not a proof of the final upgrade target. The n=3 operation must
use supported coincidence jointly, since its q equals its source dimension.
-/

noncomputable section
open Bundle Manifold Set Module MeasureTheory
open scoped ContDiff Topology

namespace GlobalEmbedding.Upgrade
open GlobalEmbedding.Paper
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

theorem supported_source_dimension_strict (hn : 4 ≤ n) :
    n < n * (n - 1) / 2 := by
  have hmul : 3 * n ≤ n * (n - 1) := by
    calc
      3 * n = n * 3 := by omega
      _ ≤ n * (n - 1) := Nat.mul_le_mul_left n (by omega)
  omega

private theorem supported_local_null_of_derived_rank
    {m k : ℕ} {Ω : Set ((Fin m → ℝ) × E)} (hn : 4 ≤ n)
    (hΩ : IsOpen Ω) {f : (Fin m → ℝ) × E → Fin k → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) {w : (Fin m → ℝ) × E} (hw : w ∈ Ω)
    (hzero : f w = 0)
    (hrank : n * (n - 1) / 2 ≤ finrank ℝ (LinearMap.range (fderiv ℝ f w).toLinearMap)) :
    ∃ U : Set ((Fin m → ℝ) × E), IsOpen U ∧ w ∈ U ∧ U ⊆ Ω ∧
      volume (Prod.fst '' (U ∩ f ⁻¹' {0})) = 0 := by
  have hnq := supported_source_dimension_strict hn
  have hdim : finrank ℝ ((Fin m → ℝ) × E) = m + n := by simp
  have hrequired : finrank ℝ ((Fin m → ℝ) × E) <
      m + finrank ℝ (LinearMap.range (fderiv ℝ f w).toLinearMap) := by
    rw [hdim]
    omega
  exact avoidance_euclidean_local_projection_null hΩ hf
    (contDiff_fst.contDiffOn : ContDiffOn ℝ ∞
      (Prod.fst : (Fin m → ℝ) × E → Fin m → ℝ) Ω) hw hzero hrequired

/-- A genuine actual supported packet admits one angle-independent tolerance
which turns the full actual paired response bounds into local avoidance of
the original supported kernels. The strict n≥4 condition is used exactly in
q>n; no conclusion removing all supported kernels is made for n=3. -/
theorem SupportedLocalWavePacket.exists_actual_supported_avoidance_tolerance
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x y : M}
    (p : SupportedLocalWavePacket F₀ hF₀ x y) (hn : 4 ≤ n)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (hx : x ∈ (A.chart i).source) (m : ℕ) :
    let B : SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x :=
      LinearMap.toContinuousLinearMap
        (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F₀ x from trueSecondForm F₀ hF₀ x)
    let T : Fin (n * (n - 1) / 2) → SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x :=
      fun j ↦ (normalSpace (I := IM) F₀ x).orthogonalProjectionOnto.comp ((p.waves j).tensor x)
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (G : (Fin m → ℝ) → M → V)
        (hG : ∀ u, ContMDiff IM 𝓘(ℝ, V) ∞ (G u))
        (Q : ∀ u z, normalSpace (I := IM) (G u) z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
        (Ω : Set ((Fin m → ℝ) × E)),
      let C := actualSupportedProbeCoordinate F₀ G hG Q A hA i x hx
      IsOpen Ω →
      (∀ z ∈ Ω, z.2 ∈ (A.chart i).target) →
      (∀ z ∈ Ω,
        ‖(normalSpace (I := IM) F₀ ((A.chart i).symm z.2)).starProjection -
          (normalSpace (I := IM) F₀ x).starProjection‖ < 1) →
      ContDiffOn ℝ ∞ C Ω →
      ∀ (w : (Fin m → ℝ) × E), w ∈ Ω →
      HasSupportedKernel (trueSecondForm (G w.1) (hG w.1) ((A.chart i).symm w.2)) →
      ∀ (σ : ℝ) (d0 d1 : Fin (n * (n - 1) / 2) → Fin m → ℝ)
        (θ : Fin (n * (n - 1) / 2) → ℝ)
        (R0 R1 : Fin (n * (n - 1) / 2) → SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x),
      0 < σ → ‖C w - B‖ < δ →
      (∀ j, fderiv ℝ C w (d0 j, 0) = (σ * Real.cos (θ j)) • T j + R0 j) →
      (∀ j, fderiv ℝ C w (d1 j, 0) = (σ * Real.sin (θ j)) • T j + R1 j) →
      (∀ j, ‖R0 j‖ ≤ σ * δ / 8) → (∀ j, ‖R1 j‖ ≤ σ * δ / 8) →
      ∃ U : Set ((Fin m → ℝ) × E), IsOpen U ∧ w ∈ U ∧ U ⊆ Ω ∧
        volume (Prod.fst '' {z | z ∈ U ∧
          HasSupportedKernel (trueSecondForm (G z.1) (hG z.1) ((A.chart i).symm z.2))}) = 0 := by
  dsimp only
  let B : SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x :=
    LinearMap.toContinuousLinearMap
      (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F₀ x from trueSecondForm F₀ hF₀ x)
  let T : Fin (n * (n - 1) / 2) → SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x :=
    fun j ↦ (normalSpace (I := IM) F₀ x).orthogonalProjectionOnto.comp ((p.waves j).tensor x)
  obtain ⟨δ, hδ, htol⟩ := exists_supported_paired_incidence_tolerance
    (P := (Fin m → ℝ) × E) p.chart T p.normal_columns
  refine ⟨δ, hδ, ?_⟩
  intro G hG Q Ω
  intro hΩ htarget hgap hC w hw hsupported σ d0 d1 θ R0 R1 hσ hclose h0 h1 hR0 hR1
  let C := actualSupportedProbeCoordinate F₀ G hG Q A hA i x hx
  have hCw : DifferentiableAt ℝ C w :=
    (hC.contDiffAt (hΩ.mem_nhds hw)).differentiableAt (by simp)
  obtain ⟨hdom, hrank⟩ := htol C w σ (fun j ↦ (d0 j, 0)) (fun j ↦ (d1 j, 0))
    θ R0 R1 hCw hσ hclose h0 h1 hR0 hR1
  let Ω' := Ω ∩ C ⁻¹' p.chart.domain
  have hΩ' : IsOpen Ω' := hC.continuousOn.isOpen_inter_preimage hΩ p.chart.isOpen_domain
  have hw' : w ∈ Ω' := ⟨hw, hdom⟩
  let f := p.chart.equation ∘ C
  have hf : ContDiffOn ℝ ∞ f Ω' :=
    p.chart.contDiffOn_equation.comp (hC.mono inter_subset_left) (fun _ hz ↦ hz.2)
  have hzero (z : (Fin m → ℝ) × E) (hz : z ∈ Ω') :
      f z = 0 ↔ HasSupportedKernel
        (trueSecondForm (G z.1) (hG z.1) ((A.chart i).symm z.2)) :=
    actualSupportedProbeCoordinate_equation_zero_iff F₀ G hG Q A hA i x hx z
      (htarget z hz.1) (hgap z hz.1) B p.chart hz.2
  obtain ⟨U, hU, hwU, hUsub, hnull⟩ := supported_local_null_of_derived_rank
    hn hΩ' hf hw' ((hzero w hw').mpr hsupported) hrank
  refine ⟨U, hU, hwU, fun z hz ↦ (hUsub hz).1, ?_⟩
  apply measure_mono_null (image_mono ?_) hnull
  intro z hz
  exact ⟨hz.1, (hzero z (hUsub hz.1)).mpr hz.2⟩

#print axioms SupportedLocalWavePacket.exists_actual_supported_avoidance_tolerance

end GlobalEmbedding.Upgrade
