import Main.EndpointStatements
import GlobalEmbedding.Targets.SmallExactImmersion
import NormalPolar.NativeProbeProvider
import Upgrade.CompactProbeAtlas

/-!
# The accepted small immersion and the actual upgrade give the original main output

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of
`thm:main` in the conclusion section. The accepted original small immersion
is invoked at radius `r/2`; the existing geometric upgrade is invoked on
that same immersion. Its literal coordinate norm is converted to the actual
Euclidean target norm before choosing the upgrade tolerance.

The upstream `NativeUpgradeProbeProvider` is deliberately explicit. This
module constructs no second copy of its normal identification or geometric
upgrade, and does not claim the original main target unconditionally.
Closing the remaining native analytic probe producer removes precisely this
remaining premise. General native uniform repair is never an input here.
-/

noncomputable section
open Set Bundle Manifold Topology GlobalEmbedding.Paper
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.Main
open GlobalEmbedding.Upgrade GlobalEmbedding.NormalPolar
open GlobalEmbedding.Continuation.RepairClosure

universe uM
variable {n : ℕ} {M : Type uM}
  [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin (n*(n+1)/2+1))
local notation "IM" => 𝓘(ℝ,E)

/-- Exact final assembly from the native analytic probe provider.

The support-covering smooth compact atlas is constructed internally.
The fixed factor converting the coordinate target norm to its Euclidean
norm is retained: the tolerance is `r/(2*(1+C))`, not an unsupported
identification of these two norms. No point of the source is chosen, so
empty and disconnected sources are both retained. All output properties
hold for the same map produced by the upgrade. -/
theorem exists_small_phase_embedding_of_native_probes
    (provider : NativeUpgradeProbeProvider
      (n := n) (N := n*(n+1)/2+1) (M := M))
    (hn : 3 ≤ n)
    (hpar : IsParallelizable (M := M) IM n)
    (metric0 : ContMDiffRiemannianMetric IM ∞ E (TangentSpace IM : M → Type _))
    (r : ℝ) (hr : 0 < r) :
    ∃ (G : M → V) (hG : ContMDiff IM 𝓘(ℝ,V) ∞ G),
      inducedMetric (I := IM) G =
        (fun x => (metric0.inner x).toLinearMap₁₂) ∧
      (∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) G x)) ∧
      PhaseRegular G hG ∧ IsClosedEmbedding G ∧
      Set.range G ⊆ Metric.ball 0 r := by
  have hhalf : 0 < r/2 := div_pos hr (by norm_num)
  obtain ⟨F,hF,hmetricF,himmF,hphaseF,hsmallF⟩ :=
    original_small_exact_immersion_candidate (n := n) (M := M)
      (by omega) hpar metric0 (r/2) hhalf
  obtain ⟨A,hA,hcompact,_hinner,hcover,_hnative⟩ :=
    exists_compact_smooth_bufferedAtlas (M := M) («E» := E)
  have hcover' : ∀ x, ∃ i, x ∈ A.support i := fun x => by
    obtain ⟨i,hi⟩ := hcover x
    exact ⟨i,interior_subset hi⟩
  let C : ℝ := ‖(EuclideanSpace.equiv (Fin (n*(n+1)/2+1)) ℝ).symm.toContinuousLinearMap‖
  have hC : 0 ≤ C := norm_nonneg _
  let epsilon : ℝ := r/(2*(1+C))
  have hepsilon : 0 < epsilon := div_pos hr (by positivity)
  have hCe : C*epsilon ≤ r/2 := by
    have heq : epsilon*(2*(1+C)) = r := by
      exact div_mul_cancel₀ r (by positivity)
    nlinarith
  obtain ⟨G,hG,hmetricG,himmG,hphaseG,hemb,hfinite,hsmallG⟩ :=
    exists_originalAtlas_sameMetric_phase_embedding_of_native_probes
      provider A hA hcompact F hF himmF hphaseF hn rfl hepsilon
  refine ⟨G,hG,?_,himmG,hphaseG,hemb,?_⟩
  · exact (funext hmetricG).trans hmetricF
  · have hbudget : probeAtlasCj A 2 (G-F) ≤ ENNReal.ofReal epsilon := by
      rw [← ENNReal.ofReal_toReal hfinite]
      exact ENNReal.ofReal_le_ofReal hsmallG.le
    rintro y ⟨x,rfl⟩
    rw [Metric.mem_ball,dist_zero_right]
    have hFbound : ‖F x‖ < r/2 :=
      (ENNReal.ofReal_lt_ofReal_iff hhalf).mp
        ((le_iSup (fun z : M => ENNReal.ofReal ‖F z‖) x).trans_lt hsmallF)
    have hdiff : ‖G x-F x‖ ≤ r/2 :=
      (norm_le_of_probeAtlasCj A hA hcover' 2 (G-F)
        hepsilon.le hbudget x).trans hCe
    calc
      ‖G x‖ = ‖(G x-F x)+F x‖ := by rw [sub_add_cancel]
      _ ≤ ‖G x-F x‖+‖F x‖ := norm_add_le _ _
      _ < r/2+r/2 := add_lt_add_of_le_of_lt hdiff hFbound
      _ = r := by ring

/-- The same constructed map has the literal main conclusion.
This wrapper does not remove the explicit native probes existence premise. -/
theorem main_conclusion_of_native_probes
    (provider : NativeUpgradeProbeProvider
      (n := n) (N := n*(n+1)/2+1) (M := M))
    (hn : 3 ≤ n)
    (hpar : IsParallelizable (M := M) IM n)
    (metric0 : ContMDiffRiemannianMetric IM ∞ E (TangentSpace IM : M → Type _))
    (r : ℝ) (hr : 0 < r) :
    ∃ (G : M → V) (hG : ContMDiff IM 𝓘(ℝ,V) ∞ G),
      inducedMetric (I := IM) G =
        (fun x => (metric0.inner x).toLinearMap₁₂) ∧
      (∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) G x)) ∧
      PhaseRegular G hG ∧ IsEmbedding G ∧
      Set.range G ⊆ Metric.ball 0 r := by
  obtain ⟨G,hG,hmetric,himm,hphase,hemb,himage⟩ :=
    exists_small_phase_embedding_of_native_probes provider hn hpar metric0 r hr
  exact ⟨G,hG,hmetric,himm,hphase,hemb.isEmbedding,himage⟩

/-- Exact full-target implication. The only unclosed premise is stated
as the native paired-probe producer on every allowed closed source; no
embedding, injectivity, incidence rank or main conclusion is assumed.
Once that producer is proved, this theorem specializes to `EndpointMainTarget`
without changing any of its original quantifiers or conclusions. -/
theorem endpoint_main_of_native_probes
    (provide : ∀ {k : ℕ} {X : Type uM}
      [TopologicalSpace X] [T2Space X] [CompactSpace X]
      [ChartedSpace (EuclideanSpace ℝ (Fin k)) X]
      [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) ∞ X]
      [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) X],
      3 ≤ k → NativeUpgradeProbeProvider
        (n := k) (N := k*(k+1)/2+1) (M := X)) :
    EndpointMainTarget.{uM} := by
  intro k X _ _ _ _ _ _ hk hpar metric0 r hr
  exact main_conclusion_of_native_probes (provide hk) hk hpar metric0 r hr

end GlobalEmbedding.Main

#print axioms GlobalEmbedding.Main.exists_small_phase_embedding_of_native_probes
#print axioms GlobalEmbedding.Main.main_conclusion_of_native_probes

#print axioms GlobalEmbedding.Main.endpoint_main_of_native_probes
