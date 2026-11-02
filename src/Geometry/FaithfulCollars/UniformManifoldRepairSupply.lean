import FaithfulCollars.ExactCompactSetup
import FaithfulCollars.OriginalPrimitiveRepairSupply

/-!
# One explicit primitive repair budget before every ambient manifold

This closes the quantifier gap of selecting a budget only after fixing M/P.
The numerical record is a definition of dimensions, fixed radii and input
profiles.  The supply theorem then quantifies over both manifold types and
all their actual finite atlases.  The bound record is produced internally.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Metric Manifold IsManifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation.FaithfulCollars
open SourceCollarsBridge
universe uM uP

def fixedOriginalPrimitiveGeometryBudget
    (n d : ℕ) (RSrc bSrc RPar bPar : ℝ) (hbSrc : 0 < bSrc) (hbPar : 0 < bPar)
    (TS TP PT ST : ℕ → ℝ) (hTS : ∀ j, 0 ≤ TS j) (hTP : ∀ j, 0 ≤ TP j)
    (hPT : ∀ j, 0 ≤ PT j) (hST : ∀ j, 0 ≤ ST j) (Ds Dp : ℕ) :
    PrimitiveGeometryBudget :=
  originalPrimitiveGeometryBudget RSrc bSrc RPar bPar hbSrc hbPar
    (originalRefinedRawProfile (EuclideanSpace ℝ (Fin n)) RSrc bSrc hbSrc) TS
    (originalRefinedRawProfile (EuclideanSpace ℝ (Fin d)) RPar (bPar/4) (by positivity)) TP PT ST
    (originalRefinedRawProfile_nonneg RSrc bSrc hbSrc) hTS
    (originalRefinedRawProfile_nonneg RPar (bPar/4) (by positivity)) hTP hPT hST Ds Dp

theorem fixedOriginalPrimitiveGeometryBudget_supply
    (n d : ℕ) (RSrc bSrc RPar bPar : ℝ) (hbSrc : 0 < bSrc) (hbPar : 0 < bPar)
    (TS TP PT ST : ℕ → ℝ) (hTS : ∀ j, 0 ≤ TS j) (hTP : ∀ j, 0 ≤ TP j)
    (hPT : ∀ j, 0 ≤ PT j) (hST : ∀ j, 0 ≤ ST j) (Ds Dp : ℕ) :
    let b := fixedOriginalPrimitiveGeometryBudget n d RSrc bSrc RPar bPar hbSrc hbPar
      TS TP PT ST hTS hTP hPT hST Ds Dp
    ∀ (M : Type uM) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
      [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
      (P : Type uP) [TopologicalSpace P] [T2Space P]
      [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
      [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P],
      ∀ (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n))) (Omega : Fin A.count → Set (EuclideanSpace ℝ (Fin n)))
        (_gS : OriginalSourceNormBuffer A Omega RSrc bSrc)
        (pc : ℕ) (chart : Fin pc → OpenPartialHomeomorph P (EuclideanSpace ℝ (Fin d)))
        (Q : Fin pc → Set (EuclideanSpace ℝ (Fin d))) (W : Fin pc → Set P),
      OriginalParameterNormBuffer chart Q W univ RPar bPar →
      IsSmoothBufferedAtlas A →
      (∀ i, chart i ∈ maximalAtlas 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P) →
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
  intro b M _ _ _ _ P _ _ _ _
  let BS := originalRefinedRawProfile (EuclideanSpace ℝ (Fin n)) RSrc bSrc hbSrc
  let BP := originalRefinedRawProfile (EuclideanSpace ℝ (Fin d)) RPar (bPar/4) (by positivity)
  have hSetup := originalCompactSetup_at_fixed_profiles (n := n) (d := d) (M := M) (P := P)
    RSrc bSrc RPar bPar hbSrc hbPar TS TP PT ST hTS hTP hPT hST Ds Dp
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
#print axioms GlobalEmbedding.Continuation.FaithfulCollars.fixedOriginalPrimitiveGeometryBudget_supply
