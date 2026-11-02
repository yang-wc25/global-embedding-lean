import NormalPolar.GlobalWaveResponsePrescribedPrimitives
import NormalPolar.GlobalWaveResponseBackgroundNormBridge

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

theorem globalWave_scaled_paired_joint
    (label : (Fin r×Bool) ↪ Fin p) (wave : (Fin p→ℝ) → Ep×M → V)
    (Su : Set (Fin p→ℝ)) (W : Set (Ep×M))
    (hJoint : ContMDiffOn ((𝓘(ℝ,(Fin p→ℝ)×Ep)).prod IM) 𝓘(ℝ,V) ∞
      (fun z : ((Fin p→ℝ)×Ep)×M => wave z.1.1 (z.1.2,z.2))
      {z | z.1.1 ∈ Su ∧ (z.1.2,z.2) ∈ W})
    (b : Ep) (hSlice : ∀ x, (b,x) ∈ W) (delta : ℝ) :
    ContMDiffOn ((𝓘(ℝ,Params)).prod IM) 𝓘(ℝ,V) ∞
      (fun z : Params×M => delta • wave (probeParameterEmbedding label z.1) (b,z.2))
      (((probeParameterEmbedding label) ⁻¹' Su) ×ˢ univ) := by
  have hMap : ContMDiff ((𝓘(ℝ,Params)).prod IM) ((𝓘(ℝ,(Fin p→ℝ)×Ep)).prod IM) ∞
      (fun z : Params×M => ((probeParameterEmbedding label z.1,b),z.2)) :=
    ((((probeParameterEmbedding label).toContinuousLinearMap.contDiff.prodMk contDiff_const).contMDiff).comp
      contMDiff_fst).prodMk contMDiff_snd
  have hScale : ContMDiff 𝓘(ℝ,V) 𝓘(ℝ,V) ∞ (fun v : V => delta • v) := by
    convert (delta • (ContinuousLinearMap.id ℝ V)).contDiff.contMDiff using 1
    funext v
    rfl
  exact hScale.comp_contMDiffOn (hJoint.comp hMap.contMDiffOn (fun z hz => ⟨hz.1,hSlice z.2⟩))

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.globalWave_scaled_paired_joint
