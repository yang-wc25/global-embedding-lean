import NormalPolar.ActualRepairModelAtlas
import Probes.Round4OriginalProbeParameters

/-!
# The same actual correction on the original paired parameter ball

This is an exact relabeling of the actual native derivative and original
mixed norm. The Pi norm, radius, and every source sampling domain are kept.
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

/-- Original paired columns of a genuine correction inherit its actual
mixed-norm bound, on the same open ball and with exact constant one. -/
theorem actualRepairModel_paired_probeAtlasCj_le_mixed
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcover : ∀ x, ∃ i, x ∈ A.support i)
    (radius : ℝ) (F : (Fin p → ℝ) → M → V)
    (hF : ContMDiffOn ((𝓘(ℝ,Fin p → ℝ)).prod IM) 𝓘(ℝ,V) ∞
      (Function.uncurry F) (Metric.ball 0 radius ×ˢ univ))
    (f : Fin A.count → (Fin (n+p) → ℝ) → Fin N → ℝ)
    (O S : Fin A.count → Set (Fin (n+p) → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i))
    (heq : ∀ i v, ‖v‖ < radius →
      ∀ x, x ∈ (EuclideanSpace.equiv (Fin n) ℝ) '' (A.chart i).target →
      f i (sourceFirstCoordinates n p (v,x)) =
        (EuclideanSpace.equiv (Fin N) ℝ) (F v ((A.chart i).symm
          ((EuclideanSpace.equiv (Fin n) ℝ).symm x))))
    (u : ProbeParameters r) (hu : ‖u‖ < radius)
    (hsource : ∀ i, (EuclideanSpace.equiv (Fin n) ℝ) '' (A.chart i).target ⊆
      actualRepairModelSlice (round4PairedParameterReindex r u) (O i))
    (hsample : ∀ i x,
      x ∈ (EuclideanSpace.equiv (Fin n) ℝ) '' ((A.chart i) '' A.support i) →
      sourceFirstCoordinates n p (round4PairedParameterReindex r u,x) ∈ S i)
    (j : ℕ) (l : Fin r) (b : Bool) :
    probeAtlasCj A j (fun x => fderiv ℝ
      (fun v : ProbeParameters r => F (round4PairedParameterReindex r v) x) u
        (Pi.single (l,b) 1)) ≤
      ⨆ i, paperMixedCoordinateCj (nx := n) (np := p) j 1 (f i) (O i) (S i) := by
  have hu' : round4PairedParameterReindex r u ∈ Metric.ball 0 radius := by
    simpa only [Metric.mem_ball,dist_zero_right,LinearIsometryEquiv.norm_map] using hu
  have he (x : M) : fderiv ℝ
      (fun v : ProbeParameters r => F (round4PairedParameterReindex r v) x) u
        (Pi.single (l,b) 1) =
      fderiv ℝ (fun v => F v x) (round4PairedParameterReindex r u)
        (Pi.single (round4PairedParameterIndex r (l,b)) 1) := by
    exact round4_paired_parameter_response_column (fun v => F v x) u (l,b)
      (actual_parameter_value_differentiableAt_of_joint A hA hcover Metric.isOpen_ball F hF _ hu' x)
  simp_rw [he]
  exact actualRepairModel_probeAtlasCj_le_mixed A hA hcover Metric.isOpen_ball F hF f O S hO hf
    (fun i v hv x hx => heq i v (by simpa only [Metric.mem_ball,dist_zero_right] using hv) x hx)
    (round4PairedParameterReindex r u) hu' hsource hsample j (round4PairedParameterIndex r (l,b))

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.actualRepairModel_paired_probeAtlasCj_le_mixed
