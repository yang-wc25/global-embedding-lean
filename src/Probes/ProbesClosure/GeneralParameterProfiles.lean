import Main.GeneralLegalWaveObserverProfiles
import NormalPolar.PassiveWaveSeedParameterRaw

/-!
# The same general-cutoff family supplies its full parameter raw profiles

The actual general source family supplies one pair of transition and phase
profile functions on the original compact source samples. The existing
passive parameter constructor transports that same data to every given
parameter chart. Its exact original sample set is retained, and the sole
transition adjustment is the existing `1 + T` allowance for the identity
parameter component.

No seed, chart, cutoff, phase, normal, source profile or sampling domain is
chosen again after the contraction or derivative orders. The original
labels still index their dependent subordinate pieces. This completes the
primitive parameter-raw boundary needed by the generic grouped background
constructor; it does not assert a repaired probe family.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold IsManifold
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.NormalPolar
open scoped ContDiff Topology Classical

namespace GlobalEmbedding.Continuation

variable {m N p r count : ℕ} {M P : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M] [TopologicalSpace P]

local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Ep" => EuclideanSpace ℝ (Fin p)
local notation "IM" => 𝓘(ℝ,D)

namespace GeneralLegalWaveRawFamily

variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {waves : Fin r → OpenSupportedLegalWave (n := m+1) F hF}
  {weight : Fin r → ℝ}

/-- The actual arbitrary-cutoff family manufactures every original grouped
parameter profile with its constants fixed before all subsequent scales. -/
theorem exists_uniform_parameter_raw_profiles
    (family : GeneralLegalWaveRawFamily F hF waves weight)
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A)
    (R : Fin A.count → Set D) (hR : ∀ i, IsCompact (R i))
    (hRt : ∀ i, R i ⊆ (A.chart i).target)
    (B : Fin count → OpenPartialHomeomorph P Ep)
    (Samples : Fin A.count × Fin count → Set (Fin (m+1+p) → ℝ))
    (hSB : ∀ idx z, parameterTensorModelEquiv (m+1) p z ∈ Samples idx →
      z.1 ∈ (B idx.2).target)
    (hSR : ∀ idx z, parameterTensorModelEquiv (m+1) p z ∈ Samples idx →
      z.2 ∈ R idx.1) :
    ∃ T Pphase : ℕ → ℝ, (∀ k, 0 < T k ∧ 0 < Pphase k) ∧
      ∀ (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
        (n j : ℕ) (ell : ℝ), 0 ≤ ell → ell ≤ 1 →
      ∀ idx : Fin A.count × Fin count,
      Nonempty (JointGroupedPrescribedParameterChartRawData (m := m) (N := N) (d := p)
        (fun _ : P => scale • F) (fun _ => contMDiff_const_rescale F hF scale)
        (fun l s _ => (family.piece l).seed.coordinate s 0)
        (fun l s (z : P × D) => (family.piece l).seed.cutoffCoordinates s (0,z.2))
        (fun l s _ => (family.piece l).seed.scaledNormal scale hs s 0)
        (fun l (z : P × M) => weight l * (waves l).phase z.2)
        (fun l s => passiveParameterChart (0 : Z) ((family.piece l).seed.physicalChart s))
        (B idx.2) (A.chart idx.1) ((B idx.2).target ×ˢ (A.chart idx.1).target)
        ((parameterTensorModelEquiv (m+1) p) ⁻¹' Samples idx)
        n j ell (family.geometryBudget (max n (j+1))) (family.cutoffBudget n)
        (family.normalBudget n) (Pphase (j+1)) T) := by
  obtain ⟨T,Pphase,hpos,hprofiles⟩ := family.exists_observation_profiles_samples
    A hA R hR hRt
  refine ⟨fun k => 1+T k,Pphase,fun k => ⟨by linarith [(hpos k).1],(hpos k).2⟩,?_⟩
  intro scale hs n j ell hell hell1 idx
  obtain ⟨profiles⟩ := hprofiles scale hs n (j+1) ell hell hell1 idx.1
  exact ⟨passiveWaveSeed_parameter_raw (B idx.2) (A.chart idx.1) (hA.chart_mem idx.1)
    (fun _ : Z => scale • F) (fun _ => contMDiff_const_rescale F hF scale)
    (fun l s => (family.piece l).seed.coordinate s)
    (fun l s => (family.piece l).seed.cutoffCoordinates s)
    (fun l s => (family.piece l).seed.scaledNormal scale hs s)
    (fun l s => (family.piece l).seed.physicalChart s)
    (fun l s => (family.piece l).seed.carrier s) n j ell
    (family.geometryBudget (max n (j+1))) (family.cutoffBudget n) (family.normalBudget n)
    hell (R idx.1) (hRt idx.1) T (fun k => (hpos k).1.le)
    (fun l (z : Z × M) => weight l * (waves l).phase z.2) (Pphase (j+1)) profiles
    ((parameterTensorModelEquiv (m+1) p) ⁻¹' Samples idx)
    (fun z hz => hSB idx z hz) (fun z hz => hSR idx z hz)⟩

end GeneralLegalWaveRawFamily
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.GeneralLegalWaveRawFamily.exists_uniform_parameter_raw_profiles
