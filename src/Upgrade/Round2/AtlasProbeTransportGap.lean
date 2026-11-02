import Round2.ProbeNormalGap

/-!
# The same chosen normal gap under a change of atlas

Once the source atlas supports cover the source, its original gap bound is
a bound at every actual point. Any complete probe family on another atlas
with literally the same `ProbeGeometry` inherits the very same gap function.
No new identification, projection or derivative bound is chosen.
-/

noncomputable section
open Bundle Filter Manifold Set
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade
open Paper

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- A genuine support cover turns the original supportwise bound into the
same bound at every actual point, including all connected components. -/
theorem ChosenProbeNormalGap.bound_all_points
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    {probe : ExactProbeFamily F₀ hF₀ A waves} (control : ChosenProbeNormalGap probe)
    (hcover : ∀ x : M, ∃ i, x ∈ A.support i)
    (t : ℝ) (ht : 0 < t) (htt : t < probe.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < probe.radius) (z : M) :
    ‖normalIdentificationOperator (n := n) F₀ (probe.map t u)
        (probe.normalIdentification t u) z -
      (normalSpace (I := IM) F₀ z).starProjection‖ ≤ control.gap t := by
  obtain ⟨i, hi⟩ := hcover z
  exact control.gap_bound t ht htt u hu i z hi

/-- A complete family on a new atlas with the SAME actual geometry inherits
the original chosen gap function. The equality is only about supplied real
geometry, not an assumed response, rank, avoidance or embedding statement. -/
def ChosenProbeNormalGap.transportSameGeometry
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A B : BufferedAtlas M E} {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    {probeA : ExactProbeFamily F₀ hF₀ A waves}
    (control : ChosenProbeNormalGap probeA)
    (hcover : ∀ x : M, ∃ i, x ∈ A.support i)
    (probeB : ExactProbeFamily F₀ hF₀ B waves)
    (hgeometry : probeB.toProbeGeometry = probeA.toProbeGeometry) :
    ChosenProbeNormalGap probeB where
  gap := control.gap
  gap_nonneg := control.gap_nonneg
  gap_tendsto := control.gap_tendsto
  gap_bound := by
    intro t ht htt u hu j z hz
    have hthreshold : probeB.threshold = probeA.threshold :=
      congrArg ProbeGeometry.threshold hgeometry
    have hradius : probeB.radius = probeA.radius :=
      congrArg ProbeGeometry.radius hgeometry
    have hbound := control.bound_all_points hcover t ht
      (hthreshold ▸ htt) u (hradius ▸ hu) z
    have hoperator := congrArg
      (fun g : ProbeGeometry (n := n) F₀ r ↦
        normalIdentificationOperator (n := n) F₀ (g.map t u) (g.normalIdentification t u) z)
      hgeometry
    change ‖normalIdentificationOperator (n := n) F₀
      (probeB.toProbeGeometry.map t u) (probeB.toProbeGeometry.normalIdentification t u) z -
      (normalSpace (I := IM) F₀ z).starProjection‖ ≤ _
    rw [hoperator]
    exact hbound

@[simp] theorem ChosenProbeNormalGap.transportSameGeometry_gap
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A B : BufferedAtlas M E} {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    {probeA : ExactProbeFamily F₀ hF₀ A waves}
    (control : ChosenProbeNormalGap probeA)
    (hcover : ∀ x : M, ∃ i, x ∈ A.support i)
    (probeB : ExactProbeFamily F₀ hF₀ B waves)
    (hgeometry : probeB.toProbeGeometry = probeA.toProbeGeometry) :
    (control.transportSameGeometry hcover probeB hgeometry).gap = control.gap := rfl

#print axioms ChosenProbeNormalGap.transportSameGeometry

end GlobalEmbedding.Upgrade
