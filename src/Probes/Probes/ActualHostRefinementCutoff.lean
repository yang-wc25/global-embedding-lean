import Probes.ActualAdaptedChartHost
import GlobalEmbedding.Paper.IncrementsGlobalPrimaryMeanBinding

/-!
# The literal produced cutoff in the original host chart

Multiply the produced Euclidean cutoff by the original host cutoff and extend
by zero through the real chart. Relative support of the original host cutoff
supplies the boundary zero germs. The conclusion is smooth on the original
open set and subordinate to the SAME produced adapted chart, without compact
source or global smoothness of arbitrary outside chart values.
-/

noncomputable section
open GlobalEmbedding.Paper Manifold Set Function Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]

def actualHostRefinementCutoff (q : OpenPartialHomeomorph (Ep × M) X)
    (theta : Ep × M → ℝ) (eta : X → ℝ) (z : Ep × M) : ℝ :=
  if z ∈ q.source then theta z*eta (q z) else 0

theorem actual_host_cutoff_smooth_supported
    (q : OpenPartialHomeomorph (Ep × M) X) (theta : Ep × M → ℝ) (eta : X → ℝ)
    (W : Set (Ep × M)) (hW : IsOpen W)
    (hTheta : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ theta W)
    (hThetaSupport : incrementsGlobalRelativeSupport W theta ⊆ q.source)
    (hq : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,X) ∞ q q.source)
    (hEta : ContDiff ℝ ∞ eta) :
    ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞
      (actualHostRefinementCutoff q theta eta) W ∧
    incrementsGlobalRelativeSupport W (actualHostRefinementCutoff q theta eta) ⊆
      incrementsGlobalRelativeSupport W theta ∩ (q.source ∩ q ⁻¹' tsupport eta) := by
  let K := incrementsGlobalRelativeSupport W theta
  let f := actualHostRefinementCutoff q theta eta
  have hpre : (Subtype.val ⁻¹' K : Set W) = tsupport (fun z : W => theta z.val) := by
    ext z
    constructor
    · rintro ⟨w,hw,he⟩
      have he' : w = z := Subtype.ext he
      simpa only [he'] using hw
    · intro hz
      exact ⟨z,hz,rfl⟩
  have hK : IsClosed (Subtype.val ⁻¹' K : Set W) := by rw [hpre]; exact isClosed_tsupport _
  have htheta0 (z : Ep × M) (hz : z ∈ W) (hn : z ∉ K) : theta z = 0 := by
    apply image_eq_zero_of_notMem_tsupport (f := fun w : W => theta w.val) (x := ⟨z,hz⟩)
    intro hs
    exact hn ⟨⟨z,hz⟩,hs,rfl⟩
  have hzero (z : Ep × M) (hz : z ∈ W) (hn : z ∉ K) : f z = 0 := by
    dsimp only [f,actualHostRefinementCutoff]
    rw [htheta0 z hz hn]
    simp
  have hsup : tsupport (fun z : W => f z.val) ⊆ (Subtype.val ⁻¹' K : Set W) := by
    apply closure_minimal _ hK
    intro z hz
    by_contra hn
    exact hz (hzero z.val z.property hn)
  have hopen : IsOpen (Subtype.val '' (Subtype.val ⁻¹' K : Set W)ᶜ) :=
    hW.isOpenMap_subtype_val _ hK.isOpen_compl
  have hsm : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ f W := by
    intro z hz
    apply ContMDiffAt.contMDiffWithinAt
    by_cases hqz : z ∈ q.source
    · have ht := hTheta.contMDiffAt (hW.mem_nhds hz)
      have he := hEta.contMDiff.contMDiffAt.comp z
        (hq.contMDiffAt (q.open_source.mem_nhds hqz))
      apply (ht.mul he).congr_of_eventuallyEq
      filter_upwards [q.open_source.mem_nhds hqz] with y hy
      exact ite_eq_left hy
    · have hn : z ∉ K := fun hk => hqz (hThetaSupport hk)
      have hzopen : z ∈ Subtype.val '' (Subtype.val ⁻¹' K : Set W)ᶜ := ⟨⟨z,hz⟩,hn,rfl⟩
      apply (contMDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
      filter_upwards [hopen.mem_nhds hzopen] with y hy
      obtain ⟨w,hw,rfl⟩ := hy
      exact hzero w.val w.property hw
  refine ⟨hsm,?_⟩
  rintro z ⟨w,hw,rfl⟩
  have hwK := hsup hw
  have hwq := hThetaSupport hwK
  refine ⟨hwK,hwq,?_⟩
  by_contra hn
  have hcont : ContinuousAt (fun y : W => q y.val) w :=
    (q.continuousOn.continuousAt (q.open_source.mem_nhds hwq)).comp continuous_subtype_val.continuousAt
  have hezero := (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto hcont
  have hfzero : (fun y : W => f y.val) =ᶠ[𝓝 w] 0 := by
    filter_upwards [hezero] with y hy
    change (if y.val ∈ q.source then theta y.val*eta (q y.val) else 0) = 0
    rw [show eta (q y.val) = 0 from hy]
    simp
  exact (notMem_tsupport_iff_eventuallyEq.mpr hfzero) hw

omit [ChartedSpace D M] in
/-- The actual native cutoff jets are retained literally in the original
host coordinates; the equality holds on the genuine target and hence in a
full ambient germ at every target point. -/
theorem actual_host_cutoff_original_coordinates
    (q : OpenPartialHomeomorph (Ep × M) X) (theta : Ep × M → ℝ) (eta : X → ℝ)
    (k : ℕ) (y : X) (hy : y ∈ q.target) :
    iteratedFDeriv ℝ k ((actualHostRefinementCutoff q theta eta) ∘ q.symm) y =
      iteratedFDeriv ℝ k (fun z => theta (q.symm z)*eta z) y := by
  have he : ((actualHostRefinementCutoff q theta eta) ∘ q.symm) =ᶠ[𝓝 y]
      (fun z => theta (q.symm z)*eta z) := by
    filter_upwards [q.open_target.mem_nhds hy] with z hz
    simp only [Function.comp_apply,actualHostRefinementCutoff,ite_eq_left (q.map_target hz),q.right_inv hz]
  exact (he.iteratedFDeriv ℝ k).eq_of_nhds

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_host_cutoff_smooth_supported
#print axioms GlobalEmbedding.Continuation.actual_host_cutoff_original_coordinates
