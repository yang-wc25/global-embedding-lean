import FaithfulCollars.GlobalFromLocalRaw
import Repair.SourceCollarNovGeometryBudget

/-!
# A manufactured internal repair Setup on compact carriers

The compact domains below are explicitly INTERNAL sampling carriers.  The
public norm sets remain `Omega` and `Q`, and the producer returns their
containment relations and the unchanged chart maps.  This constructs the
existing repair package without asserting compactness of open original
norm domains.  A final original-norm theorem must use the separately
proved comparison back to `Omega/Q`; this module does not hide that step.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Metric Manifold IsManifold
open scoped ContDiff Topology BigOperators

namespace GlobalEmbedding.Continuation.FaithfulCollars

variable {n d : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)

/-- The original positive-order transition hypothesis on joint coordinate
overlaps, including points outside the active raw supports. -/
def OriginalParameterJointTransitions {c : ℕ}
    (chart : Fin c → OpenPartialHomeomorph P Ep) (Q : Fin c → Set Ep)
    (T : ℕ → ℝ) : Prop :=
  ∀ (ip jp : Fin c) (k : ℕ), 1 ≤ k → ∀ z : Ep × Es, z.1 ∈ Q ip →
    z ∈ (((chart ip).symm.trans (chart jp)).prod (OpenPartialHomeomorph.refl Es)).source →
    ‖iteratedFDeriv ℝ k (((chart ip).symm.trans (chart jp)).prod
      (OpenPartialHomeomorph.refl Es)) z‖ ≤ T k

def OriginalSpatialJointTransitions (A : BufferedAtlas M Es)
    (Omega : Fin A.count → Set Es) (T : ℕ → ℝ) : Prop :=
  ∀ (i j : Fin A.count) (k : ℕ), 1 ≤ k → ∀ z : Ep × Es, z.2 ∈ Omega i →
    z ∈ ((OpenPartialHomeomorph.refl Ep).prod ((A.chart i).symm.trans (A.chart j))).source →
    ‖iteratedFDeriv ℝ k ((OpenPartialHomeomorph.refl Ep).prod
      ((A.chart i).symm.trans (A.chart j))) z‖ ≤ T k

/-- This constructor only consumes objects produced by the raw-pair
theorem and primitive coordinate bounds.  The full existential producer
below constructs every such object from original buffered geometry. -/
def compactSetupOfRawPair
    {pc : ℕ} (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pc) P Ep)
    (BS TS BP TP : ℕ → ℝ) (Ds Dp : ℕ)
    (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j)
    (hA : IsSmoothBufferedAtlas A)
    (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (RS : TensorRawCutoffPreparation A BS TS Ds)
    (RP : TensorLocalRawPreparation B univ BP TP Dp)
    (CS : Fin A.count → Set Es) (CP : Fin pc → Set Ep)
    (hCS : ∀ i, IsCompact (CS i)) (hCP : ∀ i, IsCompact (CP i))
    (hSTarget : ∀ i, CS i ⊆ (A.chart i).target)
    (hPTarget : ∀ i, CP i ⊆ (B.chart i).target)
    (hSSample : ∀ i, bufferedSamplingCoordinates A i ⊆ CS i)
    (hPSample : ∀ i, tensorLocalSamplingCoordinates B i ⊆ CP i)
    (radius : ℝ) (hRadius : 0 ≤ radius)
    (hSBound : ∀ i y, y ∈ CS i → ‖y‖ ≤ radius)
    (hPBound : ∀ i y, y ∈ CP i → ‖y‖ ≤ radius)
    (PT ST : ℕ → ℝ) (hPT : ∀ j, 0 ≤ PT j) (hST : ∀ j, 0 ≤ ST j)
    (hPTransition : OriginalParameterJointTransitions (n := n) B.chart CP PT)
    (hSTransition : OriginalSpatialJointTransitions (d := d) A CS ST) :
    SourceCollarNovSetup n d M P where
  source := A
  parameter := globalAtlasOfLocalRaw RP
  source_smooth := hA
  parameter_smooth := globalAtlasOfLocalRaw_smooth hB RP
  BS := BS
  TS := TS
  BP := BP
  TP := TP
  BS_nonneg := hBS
  TS_nonneg := hTS
  BP_nonneg := hBP
  TP_nonneg := hTP
  Ds := Ds
  Dp := Dp
  sourcePreparation := RS
  parameterPreparation := globalRawPreparationOfLocal RP
  Omega := CS
  Q := CP
  source_compact := hCS
  parameter_compact := hCP
  source_target := hSTarget
  parameter_target := hPTarget
  source_sampling := hSSample
  parameter_sampling := hPSample
  coordinateRadius := radius
  coordinateRadius_nonneg := hRadius
  source_bound := hSBound
  parameter_bound := hPBound
  parameterTransition := PT
  spatialTransition := ST
  parameterTransition_nonneg := hPT
  spatialTransition_nonneg := hST
  parameter_transition_jets := hPTransition
  spatial_transition_jets := hSTransition

variable [T2Space M] [T2Space P]

/-- Actual internal repair Setup, with uniform profiles and buffers fixed
before the original atlases.  Every compact carrier and raw preparation
is manufactured inside the proof.  The original domains are exposed in
the result through their exact chart identities and carrier inclusions. -/
theorem exists_uniform_originalCompactSetup
    (RSrc bSrc RPar bPar : ℝ) (hbSrc : 0 < bSrc) (hbPar : 0 < bPar)
    (TS TP PT ST : ℕ → ℝ) (hTS : ∀ j, 0 ≤ TS j) (hTP : ∀ j, 0 ≤ TP j)
    (hPT : ∀ j, 0 ≤ PT j) (hST : ∀ j, 0 ≤ ST j) (Ds Dp : ℕ) :
    ∃ BS BP : ℕ → ℝ, (∀ j, 0 ≤ BS j) ∧ (∀ j, 0 ≤ BP j) ∧
      ∀ (A : BufferedAtlas M Es) (Omega : Fin A.count → Set Es)
        (gS : OriginalSourceNormBuffer A Omega RSrc bSrc)
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
          g.source.buffer = bSrc/8 ∧ g.parameter.buffer = bPar/32 ∧
          g.BS = BS ∧ g.BP = BP ∧ g.TS = TS ∧ g.TP = TP ∧
          g.parameterTransition = PT ∧ g.spatialTransition = ST ∧
          g.Ds = Ds ∧ g.Dp = Dp ∧
          g.coordinateRadius = max (max 0 RSrc) (max 0 RPar) := by
  obtain ⟨BS, BP, hBS, hBP, hPair⟩ := exists_uniform_originalCompactRawPair
    (M := M) (P := P) (E := Es) (F := Ep) RSrc bSrc RPar bPar hbSrc hbPar TS TP Ds Dp
  refine ⟨BS, BP, hBS, hBP, ?_⟩
  intro A Omega gS pc chart Q W gP hA hChart hDs hDp hSTrans hPTrans hPJoint hSJoint
  obtain ⟨s, hASchart, hASsupport, hASdegree, hASsmooth, hMcompact,
    AP, KS, KP, hAPchart, hAPbuffer, hKS, hKP, hSampleS, hSampleP,
    rawS, rawP, hRawS, hRawP, hCompS, hCompP⟩ :=
    hPair A Omega gS (Fin pc) chart Q W univ gP hA hChart hDs hDp hSTrans hPTrans
  let A0 := originalNormBufferedAtlas A bSrc hbSrc gS.chart_buffer
  let AS := originalRefinedWorkingAtlas A0 Omega RSrc bSrc hbSrc le_rfl s
  have hAPsmooth : ∀ i, AP.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [hAPchart]
    exact hChart
  have hKSTarget : ∀ i, KS i ⊆ (AS.chart i).target :=
    fun i => (hKS i).2.trans (gS.norm_target i)
  have hKPTarget : ∀ i, KP i ⊆ (AP.chart i).target := by
    rw [hAPchart]
    exact fun i => (hKP i).2.trans (gP.norm_target i)
  let R := max (max 0 RSrc) (max 0 RPar)
  have hR : 0 ≤ R := (le_max_left 0 RSrc).trans (le_max_left _ _)
  have hSBound : ∀ i y, y ∈ KS i → ‖y‖ ≤ R := fun i y hy =>
    (gS.norm_radius i y ((hKS i).2 hy)).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hPBound : ∀ i y, y ∈ KP i → ‖y‖ ≤ R := fun i y hy =>
    (gP.norm_radius i y ((hKP i).2 hy)).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hPJoint' : OriginalParameterJointTransitions (n := n) AP.chart KP PT := by
    rw [hAPchart]
    intro ip jp k hk z hz hsource
    exact hPJoint ip jp k hk z ((hKP ip).2 hz) hsource
  have hSJoint' : OriginalSpatialJointTransitions (d := d) AS KS ST := by
    intro i j k hk z hz hsource
    exact hSJoint i j k hk z ((hKS i).2 hz) hsource
  let g := compactSetupOfRawPair AS AP BS TS BP TP Ds Dp hBS hTS hBP hTP
    hASsmooth hAPsmooth rawS rawP KS KP (fun i => (hKS i).1) (fun i => (hKP i).1)
    hKSTarget hKPTarget hSampleS hSampleP R hR hSBound hPBound PT ST hPT hST hPJoint' hSJoint'
  refine ⟨g, rfl, rfl, (fun _ => rfl), ?_, (fun _ => rfl), ?_,
    (fun i => (hKS i).2), (fun i => (hKP i).2), rfl, hAPbuffer,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro i
    exact congrFun hAPchart i
  · intro i p hp
    have h : p ∈ rawP.enlarged i := hp.1
    rwa [hRawP] at h

end GlobalEmbedding.Continuation.FaithfulCollars

#print axioms GlobalEmbedding.Continuation.FaithfulCollars.exists_uniform_originalCompactSetup
