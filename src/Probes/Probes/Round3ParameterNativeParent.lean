import Probes.Round3ParameterSupportedTransport
import Smoothing.Round3ParameterCompactParents
import Probes.Round3PreparedPrimaryPiece

/-! The SAME compact physical product parent is pulled into a native
parameter chart. The inverse chart appears literally. This provides the
actual compact refinement input; all pieces are later transported back and
summed over every parameter chart. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
variable {n d : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "𝓙" => 𝓘(ℝ,D)

def round3ParameterProductChart (B : OpenPartialHomeomorph P Ep) :
    OpenPartialHomeomorph (P × M) (Ep × M) := B.prod (OpenPartialHomeomorph.refl M)

def round3ParameterNativeParent (B : OpenPartialHomeomorph P Ep) (theta : P × M → ℝ) :
    Ep × M → ℝ := round3ParameterSupportedPullback (round3ParameterProductChart B).symm theta

theorem round3ParameterProductChart_smooth
    (B : OpenPartialHomeomorph P Ep) (hB : B ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P) :
    ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) ((𝓘(ℝ,Ep)).prod 𝓙) ∞
      (round3ParameterProductChart (M := M) B) (round3ParameterProductChart (M := M) B).source := by
  exact (contMDiffOn_of_mem_maximalAtlas hB).prodMap (contMDiff_id.contMDiffOn)

theorem round3ParameterProductChart_symm_smooth
    (B : OpenPartialHomeomorph P Ep) (hB : B ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P) :
    ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) ((𝓘(ℝ,Ep)).prod 𝓙) ∞
      (round3ParameterProductChart (M := M) B).symm (round3ParameterProductChart (M := M) B).target := by
  exact (contMDiffOn_symm_of_mem_maximalAtlas hB).prodMap (contMDiff_id.contMDiffOn)

theorem round3ParameterNativeParent_eq
    (B : OpenPartialHomeomorph P Ep) (theta : P × M → ℝ) (z : P × M)
    (hz : z.1 ∈ B.source) :
    round3ParameterNativeParent B theta (B z.1,z.2) = theta z := by
  change (if (B z.1,z.2) ∈ (round3ParameterProductChart (M := M) B).target then
    theta ((round3ParameterProductChart B).symm (B z.1,z.2)) else 0) = _
  have ht : (B z.1,z.2) ∈ (round3ParameterProductChart (M := M) B).target :=
    ⟨B.map_source hz,mem_univ _⟩
  rw [if_pos ht]
  change theta (B.symm (B z.1),z.2) = _
  rw [B.left_inv hz]

theorem round3Parameter_native_compact_parent
    [T2Space M] (B : OpenPartialHomeomorph P Ep) (hB : B ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (theta : P × M → ℝ) (hCompact : IsCompact (tsupport theta))
    (hSmooth : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ theta)
    (hSupport : tsupport theta ⊆ B.source ×ˢ (univ : Set M)) :
    ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (round3ParameterNativeParent B theta) ∧
    IsCompact (tsupport (round3ParameterNativeParent B theta)) ∧
    tsupport (round3ParameterNativeParent B theta) ⊆
      (round3ParameterProductChart (M := M) B) '' tsupport theta := by
  exact round3ParameterSupportedPullback_compact_smooth
    (round3ParameterProductChart (M := M) B).symm theta hCompact hSupport
    (round3ParameterProductChart_symm_smooth B hB) hSmooth.contMDiffOn

theorem round3Parameter_native_parent_source
    (B : OpenPartialHomeomorph P Ep) (theta : P × M → ℝ)
    (hSupport : tsupport theta ⊆ B.source ×ˢ (univ : Set M))
    (hNative : tsupport (round3ParameterNativeParent B theta) ⊆
      (round3ParameterProductChart (M := M) B) '' tsupport theta)
    (z : P × M) (hz : z.1 ∈ B.source)
    (hParent : (B z.1,z.2) ∈ tsupport (round3ParameterNativeParent B theta)) :
    z ∈ tsupport theta := by
  obtain ⟨w,hw,heq⟩ := hNative hParent
  have hzq : z ∈ (round3ParameterProductChart (M := M) B).source := ⟨hz,mem_univ _⟩
  have hwq : w ∈ (round3ParameterProductChart (M := M) B).source := hSupport hw
  have hwz : w = z := (round3ParameterProductChart (M := M) B).injOn hwq hzq heq
  simpa only [hwz] using hw

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_native_compact_parent
#print axioms GlobalEmbedding.Continuation.round3Parameter_native_parent_source
