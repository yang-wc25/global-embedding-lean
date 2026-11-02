import FaithfulCollars.CompactRepairSetup
import SourceCollarsBridge.LiftedSetup

/-!
# Uniform primitive repair geometry produced before the actual atlas

The primitive budget is an OUTPUT selected from fixed radii, degree and
transition data before any actual source/parameter charts.  Every later
original buffered geometry produces an actual compact-carrier Setup and
its proved `PrimitiveGeometryBounds`.  That bound record is not an input.

The internal Setup retains all original chart functions and covers the
same manifolds.  Its compact norm sets are explicitly exposed as subsets
of the original public norm sets.  The original-norm comparison required
at the final repair exit is a separate, substantive theorem.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Metric Manifold IsManifold
open scoped ContDiff Topology

namespace GlobalEmbedding.Continuation.FaithfulCollars
open SourceCollarsBridge

def originalPrimitiveGeometryBudget
    (RSrc bSrc RPar bPar : ℝ) (hbSrc : 0 < bSrc) (hbPar : 0 < bPar)
    (BS TS BP TP PT ST : ℕ → ℝ)
    (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j)
    (hPT : ∀ j, 0 ≤ PT j) (hST : ∀ j, 0 ≤ ST j) (Ds Dp : ℕ) :
    PrimitiveGeometryBudget where
  BS := BS
  TS := TS
  BP := BP
  TP := TP
  parameterTransition := PT
  spatialTransition := ST
  BS_nonneg := hBS
  TS_nonneg := hTS
  BP_nonneg := hBP
  TP_nonneg := hTP
  parameter_nonneg := hPT
  spatial_nonneg := hST
  Ds := Ds
  Dp := Dp
  coordinateRadius := max (max 0 RSrc) (max 0 RPar)
  coordinateRadius_nonneg := (le_max_left 0 RSrc).trans (le_max_left _ _)
  sourceBuffer := bSrc/8
  parameterBuffer := bPar/32
  sourceBuffer_pos := by positivity
  parameterBuffer_pos := by positivity

variable {n d : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)

/-- The finite actual parameter cover also supplies the compact-space
instance needed by the inherited global-parameter repair construction. -/
theorem compactSetup_parameterCompact (g : SourceCollarNovSetup n d M P) : CompactSpace P :=
  repair_source_compact_of_original_sampling g.parameter g.Q
    g.parameter_compact g.parameter_target g.parameter_sampling

variable [T2Space M] [T2Space P]

theorem exists_uniform_originalPrimitiveRepairSupply
    (RSrc bSrc RPar bPar : ℝ) (hbSrc : 0 < bSrc) (hbPar : 0 < bPar)
    (TS TP PT ST : ℕ → ℝ) (hTS : ∀ j, 0 ≤ TS j) (hTP : ∀ j, 0 ≤ TP j)
    (hPT : ∀ j, 0 ≤ PT j) (hST : ∀ j, 0 ≤ ST j) (Ds Dp : ℕ) :
    ∃ b : PrimitiveGeometryBudget,
      b.TS = TS ∧ b.TP = TP ∧ b.parameterTransition = PT ∧ b.spatialTransition = ST ∧
      b.Ds = Ds ∧ b.Dp = Dp ∧
      b.coordinateRadius = max (max 0 RSrc) (max 0 RPar) ∧
      b.sourceBuffer = bSrc/8 ∧ b.parameterBuffer = bPar/32 ∧
      ∀ (A : BufferedAtlas M Es) (Omega : Fin A.count → Set Es)
        (_gS : OriginalSourceNormBuffer A Omega RSrc bSrc)
        (pc : ℕ) (chart : Fin pc → OpenPartialHomeomorph P Ep)
        (Q : Fin pc → Set Ep) (W : Fin pc → Set P),
      OriginalParameterNormBuffer chart Q W univ RPar bPar →
      IsSmoothBufferedAtlas A →
      (∀ i, chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P) →
      A.supportDegree ≤ Ds →
      (∀ i, tensorEnlargedSupportDegree W i ≤ Dp) →
      (∀ p i j, 1 ≤ j → ∀ y ∈ (A.chart p).target,
        (A.chart p).symm y ∈ A.support i →
        ‖iteratedFDeriv ℝ j (A.chart i ∘ (A.chart p).symm) y‖ ≤ TS j) →
      (∀ p i j, 1 ≤ j → ∀ y ∈ (chart p).target,
        (chart p).symm y ∈ W i →
        ‖iteratedFDeriv ℝ j (chart i ∘ (chart p).symm) y‖ ≤ TP j) →
      OriginalParameterJointTransitions (n := n) chart Q PT →
      OriginalSpatialJointTransitions (d := d) A Omega ST →
      ∃ g : SourceCollarNovSetup n d M P,
        ∃ hSourceCount : g.source.count = A.count,
          ∃ hParameterCount : g.parameter.count = pc,
          (∀ i, g.source.chart i = A.chart (Fin.cast hSourceCount i)) ∧
          (∀ i, g.parameter.chart i = chart (Fin.cast hParameterCount i)) ∧
          (∀ i, g.source.support i = A.support (Fin.cast hSourceCount i)) ∧
          (∀ i, g.parameter.support i ⊆ W (Fin.cast hParameterCount i)) ∧
          (∀ i, g.Omega i ⊆ Omega (Fin.cast hSourceCount i)) ∧
          (∀ i, g.Q i ⊆ Q (Fin.cast hParameterCount i)) ∧
          g.source.buffer = b.sourceBuffer ∧ g.parameter.buffer = b.parameterBuffer ∧
          PrimitiveGeometryBounds b g := by
  obtain ⟨BS, BP, hBS, hBP, hSetup⟩ := exists_uniform_originalCompactSetup
    (n := n) (d := d) (M := M) (P := P) RSrc bSrc RPar bPar hbSrc hbPar
    TS TP PT ST hTS hTP hPT hST Ds Dp
  let b := originalPrimitiveGeometryBudget RSrc bSrc RPar bPar hbSrc hbPar
    BS TS BP TP PT ST hBS hTS hBP hTP hPT hST Ds Dp
  refine ⟨b, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro A Omega gS pc chart Q W gP hA hChart hDs hDp hSTrans hPTrans hPJoint hSJoint
  obtain ⟨g, hs, hp, hSchart, hPchart, hSsupport, hPsupport, hOmega, hQ,
    hSbuffer, hPbuffer, hgBS, hgBP, hgTS, hgTP, hgPT, hgST, hgDs, hgDp, hgRadius⟩ :=
    hSetup A Omega gS pc chart Q W gP hA hChart hDs hDp hSTrans hPTrans hPJoint hSJoint
  refine ⟨g, hs, hp, hSchart, hPchart, hSsupport, hPsupport, hOmega, hQ,
    hSbuffer, hPbuffer, ?_⟩
  exact {
    BS := fun j => by change g.BS j ≤ BS j; rw [hgBS]
    TS := fun j => by change g.TS j ≤ TS j; rw [hgTS]
    BP := fun j => by change g.BP j ≤ BP j; rw [hgBP]
    TP := fun j => by change g.TP j ≤ TP j; rw [hgTP]
    Ds := by change g.Ds ≤ Ds; rw [hgDs]
    Dp := by change g.Dp ≤ Dp; rw [hgDp]
    parameterTransition := fun j => by change g.parameterTransition j ≤ PT j; rw [hgPT]
    spatialTransition := fun j => by change g.spatialTransition j ≤ ST j; rw [hgST]
    coordinateRadius := by change g.coordinateRadius ≤ max (max 0 RSrc) (max 0 RPar); rw [hgRadius]
    sourceBuffer := by change bSrc/8 ≤ g.source.buffer; rw [hSbuffer]
    parameterBuffer := by change bPar/32 ≤ g.parameter.buffer; rw [hPbuffer] }

end GlobalEmbedding.Continuation.FaithfulCollars

#print axioms GlobalEmbedding.Continuation.FaithfulCollars.exists_uniform_originalPrimitiveRepairSupply
