import NormalPolar.ActualRepairModelSliceNorm
import NormalPolar.ActualRepairParameterBall

/-!
# Actual centered parameter balls retain the same native tail derivatives

An original parameter chart need not send the chosen center to zero. The
actual chart translation is retained and has derivative the identity. Its
fixed Pi ball is selected before the repair, and its membership in Q is
proved from the packet's sampling buffer without shrinking an existing ball.
-/

noncomputable section
open Set Filter Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
  GlobalEmbedding.Continuation
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade
variable {n d N c : ℕ} {M P : Type*}
  [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local instance actualRepairModelCenteredProduct : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance actualRepairModelCenteredManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,Es)) (n := ∞) P M

/-- Literal equality at every parameter, before any differentiation. -/
theorem actualRepairModel_centered_eq
    (B : TensorBufferedChartFamily (Fin c) P Ep) (b : Fin c) (p₀ : P)
    (F : P × M → Ey) (u : Fin d → ℝ) (x : M) :
    F (actualRepairParameterMap B b p₀ u,x) =
      actualRepairModelChartFamily (B.chart b) F
        ((EuclideanSpace.equiv (Fin d) ℝ) (B.chart b p₀)+u) x := by
  simp only [actualRepairParameterMap,actualRepairModelChartFamily,map_add,
    ContinuousLinearEquiv.symm_apply_apply]

/-- A chart translation preserves every actual native parameter direction,
with exact factor one. No unproved global chart inverse identity is used. -/
theorem actualRepairModel_centered_response_eq
    (B : TensorBufferedChartFamily (Fin c) P Ep) (b : Fin c) (p₀ : P)
    (F : P × M → Ey) (u direction : Fin d → ℝ) (x : M) :
    fderiv ℝ (fun v => F (actualRepairParameterMap B b p₀ v,x)) u direction =
      fderiv ℝ (fun v => actualRepairModelChartFamily (B.chart b) F v x)
        ((EuclideanSpace.equiv (Fin d) ℝ) (B.chart b p₀)+u) direction := by
  have heq : (fun v => F (actualRepairParameterMap B b p₀ v,x)) =
      (fun v => actualRepairModelChartFamily (B.chart b) F
        ((EuclideanSpace.equiv (Fin d) ℝ) (B.chart b p₀)+v) x) :=
    funext (fun v => actualRepairModel_centered_eq B b p₀ F v x)
  rw [heq]
  exact congrArg (fun L : (Fin d → ℝ) →L[ℝ] Ey => L direction)
    (fderiv_comp_add_left (𝕜 := ℝ)
      (f := fun v => actualRepairModelChartFamily (B.chart b) F v x) (x := u)
      ((EuclideanSpace.equiv (Fin d) ℝ) (B.chart b p₀)))

/-- The same source norm at each point of the chosen original parameter ball
uses the original TOTAL derivative order, with no sample-domain assumption. -/
theorem actualRepairModel_centered_spatial_le_total
    (A : BufferedAtlas M Es) (hA : IsSmoothBufferedAtlas A)
    (B : TensorBufferedChartFamily (Fin c) P Ep)
    (hB : ∀ b, B.chart b ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (Omega : Fin A.count → Set Es) (Q : Fin c → Set Ep)
    (hOmega : ∀ i, Omega i ⊆ (A.chart i).target)
    (hQ : ∀ b, Q b ⊆ (B.chart b).target)
    (hQsampling : ∀ b, tensorLocalSamplingCoordinates B b ⊆ Q b)
    (F : P × M → Ey) (hF : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ F)
    (b : Fin c) (p₀ : P) (hp₀ : p₀ ∈ B.inner b)
    (u : Fin d → ℝ) (hu : ‖u‖ < actualRepairParameterRadius B) (j : ℕ) :
    probeAtlasCj (actualRepairSamplingAtlas A Omega) j
      (fun x => F (actualRepairParameterMap B b p₀ u,x)) ≤
      paperAtlasCj j (incrementsOriginalMapCoordinates A B.chart F)
        (incrementsOriginalDifferentiation A B.chart)
        (incrementsOriginalEvaluation A B.chart Omega Q univ) := by
  have huQ : (EuclideanSpace.equiv (Fin d) ℝ) (B.chart b p₀)+u ∈
      (EuclideanSpace.equiv (Fin d) ℝ) '' Q b := by
    refine ⟨B.chart b p₀+(EuclideanSpace.equiv (Fin d) ℝ).symm u,
      actualRepairParameter_coordinates_mem_fixed_sample B Q hQsampling b p₀ hp₀ u hu,?_⟩
    simp only [map_add,ContinuousLinearEquiv.apply_symm_apply]
  simpa only [actualRepairModel_centered_eq] using
    actualRepairModelChartFamily_spatial_le_total A hA B.chart hB Omega Q hOmega hQ F hF
      b ((EuclideanSpace.equiv (Fin d) ℝ) (B.chart b p₀)+u) huQ j

/-- Actual response columns on the entire fixed parameter ball and entire
source have the literal original mixed bound; all sampling is proved. -/
theorem actualRepairModel_centered_response_le_mixed
    (A : BufferedAtlas M Es) (hA : IsSmoothBufferedAtlas A)
    (B : TensorBufferedChartFamily (Fin c) P Ep)
    (hB : ∀ b, B.chart b ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (Omega : Fin A.count → Set Es) (Q : Fin c → Set Ep)
    (hOmega : ∀ i, Omega i ⊆ (A.chart i).target)
    (hQ : ∀ b, Q b ⊆ (B.chart b).target)
    (hSampling : ∀ i, bufferedSamplingCoordinates A i ⊆ Omega i)
    (hQsampling : ∀ b, tensorLocalSamplingCoordinates B b ⊆ Q b)
    (F : P × M → Ey) (hF : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ F)
    (b : Fin c) (p₀ : P) (hp₀ : p₀ ∈ B.inner b)
    (u : Fin d → ℝ) (hu : ‖u‖ < actualRepairParameterRadius B) (a : Fin d) (j : ℕ) :
    probeAtlasCj (actualRepairSamplingAtlas A Omega) j
      (fun x => fderiv ℝ (fun v => F (actualRepairParameterMap B b p₀ v,x)) u (Pi.single a 1)) ≤
      ⨆ i, paperMixedCoordinateCj (nx := n) (np := d) j 1
        (incrementsOriginalMapCoordinates A B.chart F i)
        (incrementsOriginalDifferentiation A B.chart i)
        (incrementsOriginalEvaluation A B.chart Omega Q univ i) := by
  have huQ : (EuclideanSpace.equiv (Fin d) ℝ) (B.chart b p₀)+u ∈
      (EuclideanSpace.equiv (Fin d) ℝ) '' Q b := by
    refine ⟨B.chart b p₀+(EuclideanSpace.equiv (Fin d) ℝ).symm u,
      actualRepairParameter_coordinates_mem_fixed_sample B Q hQsampling b p₀ hp₀ u hu,?_⟩
    simp only [map_add,ContinuousLinearEquiv.apply_symm_apply]
  simpa only [actualRepairModel_centered_response_eq] using
    actualRepairModelChartFamily_response_le_mixed A hA B.chart hB Omega Q hOmega hQ hSampling F hF
      b ((EuclideanSpace.equiv (Fin d) ℝ) (B.chart b p₀)+u) huQ a j

end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.actualRepairModel_centered_response_eq
#print axioms GlobalEmbedding.NormalPolar.actualRepairModel_centered_spatial_le_total
#print axioms GlobalEmbedding.NormalPolar.actualRepairModel_centered_response_le_mixed
