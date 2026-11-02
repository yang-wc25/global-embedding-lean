import ProbesClosure.GeneralParameterNorms
import ProbesClosure.GeneralPhysicalResponses

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Function Manifold
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.NormalPolar GlobalEmbedding.Upgrade
variable {m N r : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M] [TopologicalSpace P] [T2Space P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (Fintype.card (Fin r × Bool)))) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (Fintype.card (Fin r × Bool)))) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Ep" => EuclideanSpace ℝ (Fin (Fintype.card (Fin r × Bool)))
variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {waves : Fin r → OpenSupportedLegalWave (n := m+1) F hF} {weight : Fin r → ℝ}
namespace GeneralLegalWaveRawFamily

theorem exists_physical_parameter_norms
    (family : GeneralLegalWaveRawFamily F hF waves weight)
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A)
    (Omega : Fin A.count → Set D) (hcompact : ∀ i, IsCompact (Omega i))
    (htarget : ∀ i, Omega i ⊆ (A.chart i).target) (length : ℕ)
    (B : BufferedAtlas P Ep) (amplitude : ℝ) (ha : 0 < amplitude)
    (hbuffer : B.buffer ≤ amplitude/
      (‖(EuclideanSpace.equiv (Fin (Fintype.card (Fin r × Bool))) ℝ).toContinuousLinearMap‖+1)) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ (c : ℝ) (hc : c ∈ Icc (1/2:ℝ) 1) (delta tau ell : ℝ),
      0 < tau → tau ≤ ell → ell ≤ 1 → 0 ≤ delta →
    ∀ (b : Fin B.count) (p₀ : P), p₀ ∈ B.inner b →
    ∀ (u : ProbeParameters r), ‖u‖ < actualRepairParameterRadius (tensorChartFamilyOfAtlas B) →
    ∀ (direction : ProbeParameters r),
      probeAtlasCj (actualRepairSamplingAtlas A Omega) 1
        (fun x => fderiv ℝ
          (fun v => family.centeredPhysicalPairMap c hc delta tau length B amplitude ha b p₀ v x)
            u direction) ≤ ENNReal.ofReal (C*delta*‖direction‖) ∧
      probeAtlasCj (actualRepairSamplingAtlas A Omega) 2
        (fun x => fderiv ℝ
          (fun v => family.centeredPhysicalPairMap c hc delta tau length B amplitude ha b p₀ v x)
            u direction) ≤ ENNReal.ofReal (C*delta/tau*‖direction‖) := by
  obtain ⟨C,hC,hbound⟩ := family.exists_original_parameter_norms A hA Omega hcompact htarget length
  refine ⟨C,hC,?_⟩
  intro c hc delta tau ell htau htaul hell1 hdelta b p₀ hp₀ u hu direction
  have he : (fun x => fderiv ℝ
        (fun v => family.centeredPhysicalPairMap c hc delta tau length B amplitude ha b p₀ v x)
          u direction) =
      (fun x => fderiv ℝ (fun v => family.groupedPairMap c hc delta tau length v x) u direction) := by
    funext x
    exact congrArg (fun L : ProbeParameters r →L[ℝ] V => L direction)
      (family.centeredPhysicalPairMap_fderiv c hc delta tau length
        B amplitude ha hbuffer b p₀ hp₀ u hu x)
  rw [he]
  exact hbound c hc delta tau ell htau htaul hell1 hdelta u direction

end GeneralLegalWaveRawFamily
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.GeneralLegalWaveRawFamily.exists_physical_parameter_norms
