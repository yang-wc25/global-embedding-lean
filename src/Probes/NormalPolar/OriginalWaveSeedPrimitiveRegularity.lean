import NormalPolar.GlobalWaveResponsePrescribedPrimitives
import NormalPolar.FullResponseScales

/-! Joint chart regularity is constructed for the same paired physical
components, using only the actual primitive local source data. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Continuation GlobalEmbedding.Upgrade
variable {m N p r : ℕ} {Ep M : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
local notation "Params" => ProbeParameters r

theorem originalWave_primitive_chart_joint
    (label : (Fin r×Bool) ↪ Fin p)
    (F : Ep→M→V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r→Ep→D→M)
    (vf : (l : Fin r) → (b : Ep) → (y : D) → normalSpace (I:=IM) (F b) (c l b y))
    (phase : Fin r→Ep×M→ℝ) (a : Fin r→OpenPartialHomeomorph (Ep×M) (Ep×D))
    (W : Set (Ep×M)) (K : Fin r→Set (Ep×M))
    (primitive : GlobalWavePrescribedPrimitives F hF c vf phase a W K)
    (tau : ℝ) (length : ℕ) (b : Ep) (hSlice : ∀ x, (b,x) ∈ W)
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A) (U : Set Params) (i : Fin A.count) :
    ContDiffOn ℝ ∞ (fun z : Params×D => round4PrescribedGlobalWave label F hF c vf phase tau length a
      (probeParameterEmbedding label z.1) (b,(A.chart i).symm z.2)) (U ×ˢ (A.chart i).target) := by
  have hp := round4_prescribed_global_wave_joint_smooth_local_phase label F hF c vf phase tau length a W K
    primitive.domain_open primitive.carrier_closed primitive.carrier_source primitive.chart_smooth
    primitive.A_smooth primitive.B_smooth primitive.G_smooth primitive.J_smooth primitive.T_smooth
    primitive.BR_smooth primitive.source_smooth primitive.source_support primitive.phase_smooth
  have hi : ContMDiffOn 𝓘(ℝ,Params×D) IM ∞
      (fun z : Params×D => (A.chart i).symm z.2) (U ×ˢ (A.chart i).target) :=
    (contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem i)).comp (ContinuousLinearMap.snd ℝ Params D).contDiff.contMDiff.contMDiffOn (fun z hz => hz.2)
  have he : ContMDiffOn 𝓘(ℝ,Params×D) ((𝓘(ℝ,Fin p→ℝ)).prod ((𝓘(ℝ,Ep)).prod IM)) ∞
      (fun z : Params×D => (probeParameterEmbedding label z.1,(b,(A.chart i).symm z.2)))
      (U ×ˢ (A.chart i).target) :=
    (((probeParameterEmbedding label).toContinuousLinearMap.contDiff.comp (ContinuousLinearMap.fst ℝ Params D).contDiff).contMDiff.contMDiffOn).prodMk
      (contMDiffOn_const.prodMk hi)
  exact (hp.comp he (fun z _ => ⟨mem_univ _,hSlice _⟩)).contDiffOn



end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.originalWave_primitive_chart_joint

