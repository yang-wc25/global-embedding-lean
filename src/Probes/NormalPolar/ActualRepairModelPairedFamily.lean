import NormalPolar.ActualRepairModelPaired

/-!
# Original paired parameters for the same actual repaired family

The existing Pi reindexing is a linear isometry. Joint smoothness and the
literal derivative fields therefore transfer on exactly the same ball,
including the zero-wave case, without Euclidean norm substitution.
-/

noncomputable section
open Set Filter Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.Continuation
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade
variable {n N r : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,E)
local notation "p" => Fintype.card (Fin r × Bool)

theorem actualRepairModel_paired_joint_smooth
    (radius : ℝ) (F : (Fin p → ℝ) → M → V)
    (hF : ContMDiffOn ((𝓘(ℝ,Fin p → ℝ)).prod IM) 𝓘(ℝ,V) ∞
      (Function.uncurry F) (Metric.ball 0 radius ×ˢ univ)) :
    ContMDiffOn ((𝓘(ℝ,ProbeParameters r)).prod IM) 𝓘(ℝ,V) ∞
      (fun z => F (round4PairedParameterReindex r z.1) z.2)
      (Metric.ball 0 radius ×ˢ univ) := by
  have hj : ContMDiff ((𝓘(ℝ,ProbeParameters r)).prod IM)
      ((𝓘(ℝ,Fin p → ℝ)).prod IM) ∞
      (fun z : ProbeParameters r × M => (round4PairedParameterReindex r z.1,z.2)) :=
    ((round4PairedParameterReindex r).toContinuousLinearEquiv.contDiff.contMDiff.comp
      contMDiff_fst).prodMk contMDiff_snd
  exact hF.comp hj.contMDiffOn (by
    intro z hz
    refine ⟨?_,hz.2⟩
    simpa only [Metric.mem_ball,dist_zero_right,LinearIsometryEquiv.norm_map] using hz.1)

/-- Equality as source fields transports every original spatial norm. -/
theorem actualRepairModel_paired_parameter_field
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcover : ∀ x, ∃ i, x ∈ A.support i)
    (radius : ℝ) (F : (Fin p → ℝ) → M → V)
    (hF : ContMDiffOn ((𝓘(ℝ,Fin p → ℝ)).prod IM) 𝓘(ℝ,V) ∞
      (Function.uncurry F) (Metric.ball 0 radius ×ˢ univ))
    (u : ProbeParameters r) (hu : ‖u‖ < radius) (direction : ProbeParameters r) :
    (fun x => fderiv ℝ (fun v : ProbeParameters r => F (round4PairedParameterReindex r v) x) u direction) =
      (fun x => fderiv ℝ (fun v => F v x) (round4PairedParameterReindex r u)
        (round4PairedParameterReindex r direction)) := by
  funext x
  have hu' : round4PairedParameterReindex r u ∈ Metric.ball 0 radius := by
    simpa only [Metric.mem_ball,dist_zero_right,LinearIsometryEquiv.norm_map] using hu
  exact round4_paired_parameter_derivative (fun v => F v x) u direction
    (actual_parameter_value_differentiableAt_of_joint A hA hcover Metric.isOpen_ball F hF _ hu' x)

/-- The literal original (l,b) column is the corresponding Fin column. -/
theorem actualRepairModel_paired_column_field
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcover : ∀ x, ∃ i, x ∈ A.support i)
    (radius : ℝ) (F : (Fin p → ℝ) → M → V)
    (hF : ContMDiffOn ((𝓘(ℝ,Fin p → ℝ)).prod IM) 𝓘(ℝ,V) ∞
      (Function.uncurry F) (Metric.ball 0 radius ×ˢ univ))
    (u : ProbeParameters r) (hu : ‖u‖ < radius) (l : Fin r) (b : Bool) :
    (fun x => fderiv ℝ (fun v : ProbeParameters r => F (round4PairedParameterReindex r v) x) u (Pi.single (l,b) 1)) =
      (fun x => fderiv ℝ (fun v => F v x) (round4PairedParameterReindex r u)
        (Pi.single (round4PairedParameterIndex r (l,b)) 1)) := by
  simpa only [round4PairedParameterReindex_single] using
    actualRepairModel_paired_parameter_field A hA hcover radius F hF u hu (Pi.single (l,b) 1)

end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.actualRepairModel_paired_joint_smooth
#print axioms GlobalEmbedding.NormalPolar.actualRepairModel_paired_parameter_field
