import Smoothing.Round3RepairJetLimitTransfer

/-! The fixed convolution sampling domains contain actual open buffers.
On the whole physical parameter manifold they cover every point, using the
actual parameter plateau and the original source atlas.  No compact sampling
domain is identified with an entire chart target. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold Filter
open scoped ContDiff ENNReal Topology
namespace GlobalEmbedding.Continuation
variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "IT" => 𝓘(ℝ,Es)
local instance round3RepairOriginalJetLimitChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairOriginalJetLimitIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M

variable {Data : IncrementsOriginalNativeData n d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}

variable (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)


include packet in
/-- The genuine transition from one original joint chart to another is
smooth at a common physical point and gives the literal coordinate germ. -/
theorem round3_repair_original_transition_germ
    (i j : Fin Data.atlas.count × Fin Data.parameterCount) (y : Fin (n+d) → ℝ)
    (hy : y ∈ incrementsOriginalDifferentiation Data.atlas Data.parameterChart i)
    (hp : (incrementsOriginalJointPoint Data.atlas Data.parameterChart i y).1 ∈ (Data.parameterChart j.2).source)
    (hx : (incrementsOriginalJointPoint Data.atlas Data.parameterChart i y).2 ∈ (Data.atlas.chart j.1).source) :
    let phi := parameterRound2_originalForwardCoordinates Data j ∘
      incrementsOriginalJointPoint Data.atlas Data.parameterChart i
    ContDiffAt ℝ ∞ phi y ∧ ∀ f : P × M → Ey,
      incrementsOriginalMapCoordinates Data.atlas Data.parameterChart f j ∘ phi =ᶠ[𝓝 y]
        incrementsOriginalMapCoordinates Data.atlas Data.parameterChart f i := by
  intro phi
  let e := (Data.parameterChart i.2).prod (Data.atlas.chart i.1)
  have he : e ∈ maximalAtlas 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.mem_maximalAtlas_prod (packet.domain.parameter_charts_smooth i.2)
      (packet.domain.atlas_smooth.chart_mem i.1)
  have hyE : (parameterTensorModelEquiv n d).symm y ∈ e.target := ⟨hy.2,hy.1⟩
  letI : ChartedSpace (Ep × Es) (Ep × Es) := chartedSpaceSelf (Ep × Es)
  have hInv : ContMDiffAt 𝓘(ℝ,Fin (n+d) → ℝ) 𝓘(ℝ,Ep × Es) ∞
      (incrementsOriginalJointPoint Data.atlas Data.parameterChart i) y := by
    exact ((contMDiffOn_symm_of_mem_maximalAtlas he).contMDiffAt (e.open_target.mem_nhds hyE)).comp y
      (parameterTensorModelEquiv n d).symm.contDiff.contMDiff.contMDiffAt
  let z := incrementsOriginalJointPoint Data.atlas Data.parameterChart i y
  have hForward : ContMDiffAt 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Fin (n+d) → ℝ) ∞
      (parameterRound2_originalForwardCoordinates Data j) z := by
    rw [modelWithCornersSelf_prod]
    exact (parameterTensorModelEquiv n d).contDiff.comp_contMDiffAt
      ((((contMDiffOn_of_mem_maximalAtlas (packet.domain.parameter_charts_smooth j.2)).contMDiffAt
        ((Data.parameterChart j.2).open_source.mem_nhds hp)).comp z contMDiffAt_fst).prodMk_space
        (((contMDiffOn_of_mem_maximalAtlas (packet.domain.atlas_smooth.chart_mem j.1)).contMDiffAt
          ((Data.atlas.chart j.1).open_source.mem_nhds hx)).comp z contMDiffAt_snd))
  refine ⟨(hForward.comp y hInv).contDiffAt,?_⟩
  intro f
  have hN : {w | (incrementsOriginalJointPoint Data.atlas Data.parameterChart i w).1 ∈
      (Data.parameterChart j.2).source ∧
      (incrementsOriginalJointPoint Data.atlas Data.parameterChart i w).2 ∈ (Data.atlas.chart j.1).source} ∈ 𝓝 y :=
    hInv.continuousAt.preimage_mem_nhds
      (((Data.parameterChart j.2).open_source.prod (Data.atlas.chart j.1).open_source).mem_nhds ⟨hp,hx⟩)
  filter_upwards [hN] with w hw
  change (EuclideanSpace.equiv (Fin N) ℝ)
    (f (incrementsOriginalJointPoint Data.atlas Data.parameterChart j
      (parameterRound2_originalForwardCoordinates Data j
        (incrementsOriginalJointPoint Data.atlas Data.parameterChart i w)))) = _
  rw [parameterRound2_originalForward_left_inv Data j _ hw.1 hw.2]
  rfl

/-- Buffer convergence is convergence of the same physical map in every
original observation chart, including boundary points of Ω/Q.  The real
smooth transition, rather than a norm-domain identification, proves it. -/
theorem round3_repair_original_jets_tendsto_of_buffers
    (hK : Data.parameterSet = univ)
    (f : ℕ → P × M → Ey) (g : P × M → Ey)
    (hf : ∀ j, ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ (f j))
    (hg : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ g)
    (hLimit : ∀ i a y, y ∈ packet.closedBuffer i →
      Tendsto (fun j => iteratedFDerivWithin ℝ a
        (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (f j) i) (packet.closedBuffer i) y) atTop
        (𝓝 (iteratedFDerivWithin ℝ a
          (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart g i) (packet.closedBuffer i) y))) :
    ∀ i a y, y ∈ incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i →
      Tendsto (fun j => iteratedFDeriv ℝ a
        (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (f j) i) y) atTop
        (𝓝 (iteratedFDeriv ℝ a
          (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart g i) y)) := by
  intro i a y hy
  have hyData : y ∈ incrementsOriginalDifferentiation Data.atlas Data.parameterChart i := by
    rwa [packet.chart_eq] at hy
  let z := incrementsOriginalJointPoint Data.atlas Data.parameterChart i y
  obtain ⟨b,hp,hx,hBuffer⟩ := packet.closedBuffer_cover hK z
  have hTransition := round3_repair_original_transition_germ packet i b y hyData hp hx
  let phi := parameterRound2_originalForwardCoordinates Data b ∘
    incrementsOriginalJointPoint Data.atlas Data.parameterChart i
  have hPhi : ContDiffAt ℝ ∞ phi y := hTransition.1
  have hImage : phi y ∈ packet.closedBuffer b := hBuffer
  have hF (j : ℕ) : ContDiffOn ℝ ∞
      (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (f j) b) (packet.closedBuffer b) :=
    (parameterRound2_originalMapCoordinates_contDiffOn Data.atlas Data.parameterChart
      packet.domain.atlas_smooth packet.domain.parameter_charts_smooth (f j) (hf j) b).mono
        (fun w hw => by
          have h := (packet.closedBuffer_subset_samples b hw).1
          rwa [packet.chart_eq] at h)
  have hG : ContDiffOn ℝ ∞
      (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart g b) (packet.closedBuffer b) :=
    (parameterRound2_originalMapCoordinates_contDiffOn Data.atlas Data.parameterChart
      packet.domain.atlas_smooth packet.domain.parameter_charts_smooth g hg b).mono
        (fun w hw => by
          have h := (packet.closedBuffer_subset_samples b hw).1
          rwa [packet.chart_eq] at h)
  have h := round3_repair_jet_limit_comp
    (fun j => incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (f j) b)
    (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart g b) phi (packet.closedBuffer b)
    (packet.closedBuffer_open b) hF hG y hPhi hImage a (fun r _ => by
      have h := hLimit b r (phi y) hImage
      simpa only [packet.chart_eq,iteratedFDerivWithin_of_isOpen r (packet.closedBuffer_open b) hImage] using h)
  have hEq (f' : P × M → Ey) :
      iteratedFDeriv ℝ a (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart f' b ∘ phi) y =
      iteratedFDeriv ℝ a (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart f' i) y :=
    ((hTransition.2 f').iteratedFDeriv ℝ a).eq_of_nhds
  simpa only [hEq,packet.chart_eq] using h

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_repair_original_transition_germ
#print axioms GlobalEmbedding.Continuation.round3_repair_original_jets_tendsto_of_buffers
