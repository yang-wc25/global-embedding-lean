import UpgradeContinuation.ReferenceReserves
import SourceCollarsBridge.LiftedSetup
import Repair.ClosureNovClassSmoothing

/-!
# A fixed native input class manufactured from the original map

Every numerical profile is selected from the actual compact source Setup
and the actual reference map.  The original qualitative phase and immersion
conditions supply positive quantitative reserves.  The existing reference
factory can consequently manufacture its native datum and fixed smoothing
packet without asking for either as an input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold IsManifold Bundle GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal Classical

namespace GlobalEmbedding.Continuation.UpgradeContinuation
open SourceCollarsBridge
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {m N : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Z" => ZeroParameter
local notation "IM" => 𝓘(ℝ,D)

private local instance referenceProductChart : ChartedSpace (Z × D) (Z × M) :=
  prodChartedSpace Z Z D M
private local instance referenceProductManifold : IsManifold 𝓘(ℝ,Z × D) ∞ (Z × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Z)) (I' := IM) (n := ∞) Z M

/-- The primitive profile is the actual already constructed geometry's
profile.  No estimate of a generated profile is postulated. -/
def actualPrimitiveBudget (g : SourceCollarNovSetup (m+1) 0 M Z) : PrimitiveGeometryBudget where
  BS := g.BS
  TS := g.TS
  BP := g.BP
  TP := g.TP
  parameterTransition := g.parameterTransition
  spatialTransition := g.spatialTransition
  BS_nonneg := g.BS_nonneg
  TS_nonneg := g.TS_nonneg
  BP_nonneg := g.BP_nonneg
  TP_nonneg := g.TP_nonneg
  parameter_nonneg := g.parameterTransition_nonneg
  spatial_nonneg := g.spatialTransition_nonneg
  Ds := g.Ds
  Dp := g.Dp
  coordinateRadius := g.coordinateRadius
  coordinateRadius_nonneg := g.coordinateRadius_nonneg
  sourceBuffer := g.source.buffer
  parameterBuffer := g.parameter.buffer
  sourceBuffer_pos := g.source.buffer_pos
  parameterBuffer_pos := g.parameter.buffer_pos

omit [T2Space M] [CompactSpace M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)] in
theorem actualPrimitiveBounds (g : SourceCollarNovSetup (m+1) 0 M Z) :
    PrimitiveGeometryBounds (actualPrimitiveBudget g) g where
  BS := fun _ => le_rfl
  TS := fun _ => le_rfl
  BP := fun _ => le_rfl
  TP := fun _ => le_rfl
  Ds := le_rfl
  Dp := le_rfl
  parameterTransition := fun _ => le_rfl
  spatialTransition := fun _ => le_rfl
  coordinateRadius := le_rfl
  sourceBuffer := le_rfl
  parameterBuffer := le_rfl

/-- A fixed allowed class for the literal original map.  Its parameter
charts are identity maps, so it can enter the passive probe producer. -/
theorem exists_originalReference_allowedClass
    (hdim : 2 ≤ m+1) (hambient : (m+1)*(m+2)/2 < N)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (himm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x))
    (hphase : PhaseRegular F hF) :
    ∃ c : ClosureNovFixedClass m 0 N M Z,
      c.AllowedMap (fun z : Z × M => F z.2) ∧
      (∀ i, c.geometry.parameter.chart i = OpenPartialHomeomorph.refl Z) ∧
      c.geometry.Q = (fun _ => univ) ∧
      (∀ i, IsCompact (c.geometry.source.support i)) ∧
      (∀ x, ∃ i, x ∈ c.geometry.source.support i) := by
  obtain ⟨g,hparameter,hQ,hforward,hcompact,hcover⟩ :=
    exists_zeroParameter_compactSetup (n := m+1) (M := M)
  obtain ⟨lower,margin,hlower,hmargin,hres⟩ :=
    exists_nativeReference_coordinate_reserves g.source g.source_smooth g.Omega
      g.source_compact g.source_target hdim F hF himm hphase
  let F0 : Z × M → V := fun z => F z.2
  have hF0 : ContMDiff 𝓘(ℝ,Z × D) 𝓘(ℝ,V) ∞ F0 := by
    rw [modelWithCornersSelf_prod]
    exact hF.comp contMDiff_snd
  let R : ℕ → ℝ := fun j =>
    (paperAtlasCj j (incrementsOriginalMapCoordinates g.source g.parameter.chart F0)
      g.differentiation g.samples).toReal
  have hR (j : ℕ) : 0 ≤ R j := ENNReal.toReal_nonneg
  let b := actualPrimitiveBudget g
  let hb := actualPrimitiveBounds g
  let c : ClosureNovFixedClass m 0 N M Z := {
    numerical := b.numericalSetup R hR lower margin hlower hmargin hdim hambient
    geometry := hb.liftedSetup
    geometryBounds := hb.geometryBounds R hR lower margin hlower hmargin hdim hambient }
  have hallowed : c.AllowedMap F0 := {
    smooth := hF0
    map_bounds := fun _ _ => le_rfl
    ellipticity := by
      intro p i y hy v
      exact (hres i p y hy).1 v
    phase_margin := by
      intro i z hz
      have hx := congrArg Prod.snd ((parameterTensorModelEquiv (m+1) 0).symm_apply_apply z)
      change incrementsOriginalSourcePoint (parameterTensorModelEquiv (m+1) 0 z) = z.2 at hx
      have hy : z.2 ∈ c.geometry.Omega i.1 := by simpa only [hx] using hz.2.1
      change z.2 ∈ g.Omega i.1 at hy
      exact (hres i.1 z.1 z.2 hy).2 }
  have hchart : ∀ i, g.parameter.chart i = OpenPartialHomeomorph.refl Z := by
    rw [hparameter]
    exact fun _ => rfl
  exact ⟨c,hallowed,hchart,hQ,hcompact,hcover⟩

end GlobalEmbedding.Continuation.UpgradeContinuation

#print axioms GlobalEmbedding.Continuation.UpgradeContinuation.exists_originalReference_allowedClass
