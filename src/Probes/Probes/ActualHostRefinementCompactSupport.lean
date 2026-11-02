import Probes.ActualHostRefinementCutoff
import Smoothing.ParameterRound2GlobalMeanSupport

/-! Actual absolute support for a compact native refinement cutoff.

The local native bump has compact support inside the real host target. Its
inverse image is therefore a compact carrier inside W. On a Hausdorff source
this carrier is closed, so the literal zero extension has compact absolute
support. This is a proved supplier for the secondary raw geometry's closed
support field, not an identification of relative and absolute supports.
No compactness of the entire source manifold is required.
-/

noncomputable section
open GlobalEmbedding.Paper Manifold Set Function Filter
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]

theorem actual_host_cutoff_compact_global_support
    (q : OpenPartialHomeomorph (Ep × M) X) (theta : Ep × M → ℝ) (eta : X → ℝ)
    (W : Set (Ep × M)) (hW : IsOpen W)
    (hTheta : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ theta W)
    (hThetaSupport : incrementsGlobalRelativeSupport W theta ⊆ q.source)
    (hq : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,X) ∞ q q.source)
    (hEta : ContDiff ℝ ∞ eta) (hCompact : IsCompact (tsupport eta))
    (hTarget : tsupport eta ⊆ q.target) (hMap : MapsTo q.symm (tsupport eta) W) :
    let f := actualHostRefinementCutoff q theta eta
    IsCompact (tsupport f) ∧ tsupport f ⊆ W ∧
      ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ f ∧
      tsupport f ⊆ incrementsGlobalRelativeSupport W theta ∩ (q.source ∩ q ⁻¹' tsupport eta) := by
  intro f
  have hCarrier : IsCompact (q.symm '' tsupport eta) :=
    hCompact.image_of_continuousOn (q.symm.continuousOn.mono hTarget)
  have hSourceSupport : Function.support f ⊆ q.symm '' tsupport eta := by
    intro z hz
    have hqz : z ∈ q.source := by
      by_contra hn
      exact hz (by simp only [f,actualHostRefinementCutoff,ite_eq_right hn])
    have hnonzero : eta (q z) ≠ 0 := by
      intro he
      exact hz (by simp only [f,actualHostRefinementCutoff,ite_eq_left hqz,he,mul_zero])
    exact ⟨q z,subset_tsupport _ hnonzero,q.left_inv hqz⟩
  have hSupport : tsupport f ⊆ q.symm '' tsupport eta :=
    closure_minimal hSourceSupport hCarrier.isClosed
  have hSupportW : tsupport f ⊆ W := by
    intro z hz
    obtain ⟨y,hy,rfl⟩ := hSupport hz
    exact hMap hy
  obtain ⟨hSmooth,hRelative⟩ := actual_host_cutoff_smooth_supported q theta eta W hW
    hTheta hThetaSupport hq hEta
  have hGlobal : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ f := by
    intro z
    by_cases hz : z ∈ W
    · exact hSmooth.contMDiffAt (hW.mem_nhds hz)
    · have hn : z ∉ tsupport f := fun hs => hz (hSupportW hs)
      exact (contMDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
        (notMem_tsupport_iff_eventuallyEq.mp hn)
  refine ⟨hCarrier.of_isClosed_subset (isClosed_tsupport f) hSupport,hSupportW,hGlobal,?_⟩
  rw [parameterRound2_global_relativeSupport_eq W hW] at hRelative
  intro z hz
  exact hRelative ⟨hSupportW hz,hz⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_host_cutoff_compact_global_support
