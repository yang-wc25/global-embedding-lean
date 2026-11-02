import Probes.Round3ParameterCrossHostConjugation
import Probes.Round3ParameterPrimaryPhysicalPoint

/-! Real regularity and phase adaptation of the actual cross-B native
chart. The coordinate change is the full nonlinear transition between the
original parameter charts. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3Parameter_primary_native_preserves_phase
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (ip : Fin Data.parameterCount) (nu : Fin Data.primaryCount) (W : Set (Ep × M))
    (piece : Round3PreparedPrimaryPiece Data ip nu W) :
    Round3ParameterChartPreserves piece.native ∧
    ∀ z ∈ piece.native.source, (piece.native z).2 0 =
      Data.phase nu ((Data.parameterChart ip).symm z.1,(Data.atlas.chart piece.host).symm z.2) := by
  have hg := actual_host_slice_geometry_inputs (Data.atlas.chart piece.host)
    (hd.atlas_smooth.chart_mem piece.host) piece.native _ piece.slices piece.data
  have hf (z : X) (hz : z ∈ piece.native.source) :
      (piece.native z).1 = z.1 ∧ (piece.native z).2 0 =
        Data.phase nu ((Data.parameterChart ip).symm z.1,(Data.atlas.chart piece.host).symm z.2) := by
    let q := actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart piece.host)
    have hqz : z ∈ q.target := hg.1 hz
    have hsrc : q.symm z ∈ (actualHostAdaptedChart (Data.atlas.chart piece.host) piece.native).source :=
      ⟨q.map_target hqz,by change q (q.symm z) ∈ piece.native.source; rwa [q.right_inv hqz]⟩
    have hh := piece.data.2.2.2.1 (q.symm z) hsrc
    change (piece.native (q (q.symm z))).1 = z.1 ∧
      (piece.native (q (q.symm z))).2 0 = _ at hh
    rw [q.right_inv hqz] at hh
    exact hh
  exact ⟨fun z hz => (hf z hz).1,fun z hz => (hf z hz).2⟩

theorem round3Parameter_cross_native_smooth
    (Bpiece Bobserver : OpenPartialHomeomorph P Ep)
    (hBp : Bpiece ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (hBo : Bobserver ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (b : OpenPartialHomeomorph X X) (hb : ContDiffOn ℝ ∞ b b.source)
    (hbi : ContDiffOn ℝ ∞ b.symm b.target) :
    let bC := round3ParameterCrossNativeChart Bpiece Bobserver b
    ContDiffOn ℝ ∞ bC bC.source ∧ ContDiffOn ℝ ∞ bC.symm bC.target := by
  intro bC
  let C := Bpiece.symm.trans Bobserver
  let q := C.prod (OpenPartialHomeomorph.refl D)
  have hC : ContDiffOn ℝ ∞ C C.source :=
    (round3Parameter_partial_trans_smooth Bpiece.symm Bobserver
      (contMDiffOn_symm_of_mem_maximalAtlas hBp) (contMDiffOn_of_mem_maximalAtlas hBo)).contDiffOn
  have hCi : ContDiffOn ℝ ∞ C.symm C.target :=
    (round3Parameter_partial_trans_symm_smooth Bpiece.symm Bobserver
      (contMDiffOn_of_mem_maximalAtlas hBp) (contMDiffOn_symm_of_mem_maximalAtlas hBo)).contDiffOn
  have hq : ContDiffOn ℝ ∞ q q.source := hC.prodMap contDiff_id.contDiffOn
  have hqi : ContDiffOn ℝ ∞ q.symm q.target := hCi.prodMap contDiff_id.contDiffOn
  exact ⟨(round3Parameter_partial_trans_smooth (q.symm.trans b) q
      (round3Parameter_partial_trans_smooth q.symm b hqi.contMDiffOn hb.contMDiffOn) hq.contMDiffOn).contDiffOn,
    (round3Parameter_partial_trans_symm_smooth (q.symm.trans b) q
      (round3Parameter_partial_trans_symm_smooth q.symm b hq.contMDiffOn hbi.contMDiffOn) hqi.contMDiffOn).contDiffOn⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_primary_native_preserves_phase
#print axioms GlobalEmbedding.Continuation.round3Parameter_cross_native_smooth
