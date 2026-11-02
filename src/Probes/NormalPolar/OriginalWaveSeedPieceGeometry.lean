import NormalPolar.OriginalWaveSeedRescaledFamily

/-! The actual ordinary-partition pieces recover the original legal value
and phase. Their carriers remain genuine closed supports,
with the exact same original phase and parameter label. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade GlobalEmbedding.Continuation GlobalEmbedding.Offline

variable {m N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {w : LocalLegalWave (n := m+1) F hF} {weight : ℝ}

namespace OriginalWaveSeedRefinement

def pieceCarrier (d : OriginalWaveSeedRefinement (m := m) F hF w weight)
    (i : Fin d.count) : Set M :=
  tsupport (fun x : M => d.cutoff i (default,x))

def pieceValue (d : OriginalWaveSeedRefinement (m := m) F hF w weight)
    (i : Fin d.count) : M → V :=
  fun x => d.cutoff i (default,x) • (w.normal x : V)

theorem pieceValue_zero (d : OriginalWaveSeedRefinement (m := m) F hF w weight)
    (i : Fin d.count) (x : M) (hx : x ∉ d.pieceCarrier i) : d.pieceValue i x = 0 := by
  change d.cutoff i (default,x) • (w.normal x : V) = 0
  rw [image_eq_zero_of_notMem_tsupport hx,zero_smul]

theorem pieceCarrier_closed (d : OriginalWaveSeedRefinement (m := m) F hF w weight)
    (i : Fin d.count) : IsClosed (d.pieceCarrier i) := isClosed_tsupport _

theorem pieceCarrier_projection (d : OriginalWaveSeedRefinement (m := m) F hF w weight)
    (i : Fin d.count) : tsupport (d.cutoff i) ⊆ Prod.snd ⁻¹' d.pieceCarrier i := by
  have he : d.cutoff i = (fun x : M => d.cutoff i (default,x)) ∘ Prod.snd := by
    funext z
    exact congrArg (fun b : Z => d.cutoff i (b,z.2)) (Subsingleton.elim _ _)
  rw [he]
  exact tsupport_comp_subset_preimage _ continuous_snd

theorem sum_pieceValue (d : OriginalWaveSeedRefinement (m := m) F hF w weight)
    (x : M) : ∑ i, d.pieceValue i x = w.value x :=
  d.sum_value (default,x)

end OriginalWaveSeedRefinement

namespace OriginalWaveSeedBuffer
variable {d : OriginalWaveSeedRefinement (m := m) F hF w weight} {i : Fin d.count}

theorem spatial_inverse_eq (b b' : OriginalWaveSeedBuffer d i) (y : D) :
    b'.spatialChart.symm y = b.spatialChart.symm y := by
  rw [b'.spatial_inverse_original (default,y),b.spatial_inverse_original (default,y)]

theorem piece_phase_binding (b : OriginalWaveSeedBuffer d i)
    (hweight : 0 < weight) (y : D) (hy : y ∈ b.spatialChart.target) :
    y 0/weight = w.phase (b.spatialChart.symm y) := by
  apply (div_eq_iff hweight.ne').mpr
  exact (b.spatialChart_inverse_phase y hy).symm.trans (mul_comm _ _)

theorem piece_amplitude_binding (b b' : OriginalWaveSeedBuffer d i)
    (c : ℝ) (hc : c ≠ 0) (y : D) :
    d.cutoffCoordinates i (default,y) •
      (actualRescaledNormal F hF c hc (b'.spatialChart.symm y)
        (w.normal (b'.spatialChart.symm y)) : V) =
      d.pieceValue i (b.spatialChart.symm y) := by
  have hi : (d.chart i).symm (default,y) = (default,b.spatialChart.symm y) := by
    apply Prod.ext (Subsingleton.elim _ _)
    exact (b.spatial_inverse_original (default,y)).symm
  change d.cutoff i ((d.chart i).symm (default,y)) • (w.normal (b'.spatialChart.symm y) : V) =
    d.cutoff i (default,b.spatialChart.symm y) • (w.normal (b.spatialChart.symm y) : V)
  rw [hi,b.spatial_inverse_eq b' y]

end OriginalWaveSeedBuffer

end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedRefinement.sum_pieceValue
#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedBuffer.piece_amplitude_binding

