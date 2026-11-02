import Upgrade.IncidenceSupportedGeometry
import Upgrade.SupportedProbeAvoidance
import GlobalEmbedding.Paper.AvoidanceEuclideanLocalNull

/-!
# Actual supported-coincidence avoidance in dimension three

The rank threshold is derived from the actual supported legal packet, the
actual legal value directions and the actual tangent image. Avoidance applies
to the literal supported kernel together with equality of the two actual
values. This theorem does not remove all supported kernels in dimension three.

The remaining numerical hypotheses are actual derivative error estimates;
they are not a supplied incidence rank, null set, separation or embedding.
The full probes interface and the quantitative selected-normal-identification
bridge must still discharge them in the global chain.
-/

noncomputable section
open Function Manifold Module Set MeasureTheory
open scoped ContDiff Topology

namespace GlobalEmbedding.Upgrade
open Paper SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

theorem actual_probe_pair_local_null_of_rank
    {r : ℕ} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W]
    {Ω : Set (ProbeParameters r × (E × E))} (hΩ : IsOpen Ω)
    {f : ProbeParameters r × (E × E) → W} (hf : ContDiffOn ℝ ∞ f Ω)
    {w : ProbeParameters r × (E × E)} (hw : w ∈ Ω) (hzero : f w = 0)
    (hrank : 2 * n + 1 ≤ finrank ℝ (fderiv ℝ f w).range) :
    ∃ U : Set (ProbeParameters r × (E × E)), IsOpen U ∧ w ∈ U ∧ U ⊆ Ω ∧
      volume ((fun z : ProbeParameters r × (E × E) ↦ probeParameterCoordinates r z.1) ''
        (U ∩ f ⁻¹' {0})) = 0 := by
  have hdim : finrank ℝ (ProbeParameters r × (E × E)) =
      finrank ℝ (ProbeParameters r) + 2 * n := by simp; omega
  have hrequired : finrank ℝ (ProbeParameters r × (E × E)) <
      finrank ℝ (ProbeParameters r) + finrank ℝ (fderiv ℝ f w).range := by
    rw [hdim]
    omega
  exact avoidance_euclidean_local_projection_null hΩ hf
    (((probeParameterCoordinates r).contDiff.comp contDiff_fst).contDiffOn : ContDiffOn ℝ ∞
      (fun z : ProbeParameters r × (E × E) ↦ probeParameterCoordinates r z.1) Ω)
    hw hzero hrequired

namespace SupportedJointWavePacket

/-- One positive, angle-independent tolerance suffices for local avoidance of
the original supported coincidences. The principal weights can be fixed
auxiliary weights before the wave list is submitted to probes. -/
theorem exists_actual_supported_coincidence_avoidance_tolerance
    {F₀ : M → EuclideanSpace ℝ (Fin N)}
    {hF₀ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F₀} {x y : M}
    (p : SupportedJointWavePacket (n := n) (N := N) F₀ hF₀ x y)
    (hn : n = 3) (himm : Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (hx : x ∈ (A.chart i).source)
    (mu : Fin (n * (n - 1) / 2 + n) → Fin 2 → ℝ)
    (hmu : ∀ l b, 0 < mu l b) (hne : ∀ l, mu l 0 ≠ mu l 1) :
    let principal := supportedJointPrincipalColumn (incidenceActualTangent (n := n) F₀ x)
      p.equationColumns p.valueNormals mu
    ∃ eps > 0,
      ∀ (r : ℕ) (data : IncidenceData p A hA i hx (ProbeParameters r))
        (U : Set (ProbeParameters r)) (Ω : Set ((ProbeParameters r) × (E × E))),
      IsOpen U → IsOpen Ω → data.sigma ≠ 0 → data.a ≠ 0 →
      ContMDiffOn ((𝓘(ℝ, ProbeParameters r)).prod IM) 𝓘(ℝ, V) ∞
        (Function.uncurry data.map) (U ×ˢ univ) →
      ContMDiffOn ((𝓘(ℝ, ProbeParameters r)).prod IM) 𝓘(ℝ, V →L[ℝ] V) ∞
        (fun z : (ProbeParameters r) × M ↦ normalIdentificationOperator (n := n)
          F₀ (data.map z.1) (data.identification z.1) z.2) (U ×ˢ univ) →
      (∀ z ∈ Ω, z.1 ∈ U ∧ z.2.1 ∈ (A.chart i).target ∧
        z.2.2 ∈ (A.chart data.secondChart).target) →
      (∀ z ∈ Ω, ‖(normalSpace (I := IM) F₀ ((A.chart i).symm z.2.1)).starProjection -
        (normalSpace (I := IM) F₀ x).starProjection‖ < 1) →
      (∀ z ∈ Ω, actualSupportedProbeCoordinate F₀ data.map data.smooth data.identification
        A hA i x hx (z.1, z.2.1) ∈ p.chart.domain) →
      ∀ w ∈ Ω,
      HasSupportedKernel (trueSecondForm (data.map w.1) (data.smooth w.1)
        ((A.chart i).symm w.2.1)) →
      data.map w.1 ((A.chart i).symm w.2.1) =
        data.map w.1 ((A.chart data.secondChart).symm w.2.2) →
      ∀ d : (Fin (n * (n - 1) / 2 + n) × Fin 2) → ProbeParameters r,
      (∀ l, ‖fderiv ℝ (fun v ↦ data.incidence (v, w.2)) w.1 (d l) - principal l‖ ≤ eps) →
      (∀ v, ‖fderiv ℝ (fun s ↦ data.incidence (w.1, s, w.2.2)) w.2.1 (data.a • v) -
        (0, p.sourceReferenceDerivative A hA i hx v)‖ ≤ eps * ‖v‖) →
      ∃ W : Set ((ProbeParameters r) × (E × E)), IsOpen W ∧ w ∈ W ∧ W ⊆ Ω ∧
        volume ((fun z : ProbeParameters r × (E × E) ↦ probeParameterCoordinates r z.1) '' {z | z ∈ W ∧
          HasSupportedKernel (trueSecondForm (data.map z.1) (data.smooth z.1)
            ((A.chart i).symm z.2.1)) ∧
          data.map z.1 ((A.chart i).symm z.2.1) =
            data.map z.1 ((A.chart data.secondChart).symm z.2.2)}) = 0 := by
  dsimp only
  have ht := exists_parameter_independent_actual_joint_rank_tolerance (n := n) (N := N)
    p himm A hA i hx mu hmu hne
  obtain ⟨eps, heps, htol⟩ := ht
  refine ⟨eps, heps, ?_⟩
  intro r data U Ω hU hΩ hσ ha hmap hQ htarget hgap hdom w hw hsupp hcoin d hp hs
  have hJ := data.contDiffOn_incidence (A := A) (hA := hA) (i := i) (hx := hx)
    hU hmap hQ htarget hdom
  have hDw : DifferentiableAt ℝ data.incidence w :=
    (hJ.contDiffAt (hΩ.mem_nhds hw)).differentiableAt (by simp)
  have hrank := htol (ProbeParameters r) data w hDw d hp hs
  have hzero : data.incidence w = 0 :=
    (data.zero_iff (A := A) (hA := hA) (i := i) (hx := hx) w hσ ha
      (htarget w hw).2.1 (hgap w hw) (hdom w hw)).mpr ⟨hsupp, hcoin⟩
  have hrank' : 2 * n + 1 ≤ finrank ℝ (fderiv ℝ data.incidence w).range := by
    subst n
    norm_num at hrank ⊢
    omega
  have hnullExists := actual_probe_pair_local_null_of_rank (n := n) (r := r)
    hΩ hJ hw hzero hrank'
  obtain ⟨W, hW, hwW, hWsub, hnull⟩ := hnullExists
  refine ⟨W, hW, hwW, hWsub, ?_⟩
  apply measure_mono_null (image_mono ?_) hnull
  intro z hz
  exact ⟨hz.1, (data.zero_iff (A := A) (hA := hA) (i := i) (hx := hx) z hσ ha
    (htarget z (hWsub hz.1)).2.1 (hgap z (hWsub hz.1)) (hdom z (hWsub hz.1))).mpr hz.2⟩

end SupportedJointWavePacket

#print axioms SupportedJointWavePacket.exists_actual_supported_coincidence_avoidance_tolerance

end GlobalEmbedding.Upgrade
