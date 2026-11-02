import ProbesClosure.GeneralPhysicalIdentity
import ProbesClosure.GeneralPaperResponses

/-! The original value and Hessian derivatives are preserved when the physical
parameter point moves through the original parameter chart. The amplitude
condition is an initialization condition on the original buffer. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Function Manifold
open scoped ContDiff Topology BigOperators Classical
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
private local instance physicalHessianSemi : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance physicalHessianNorm : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance physicalHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace
variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {waves : Fin r → OpenSupportedLegalWave (n := m+1) F hF} {weight : Fin r → ℝ}
namespace GeneralLegalWaveRawFamily

def centeredPhysicalPairMap
    (family : GeneralLegalWaveRawFamily F hF waves weight)
    (c : ℝ) (hc : c ∈ Icc (1/2:ℝ) 1) (delta tau : ℝ) (length : ℕ)
    (B : BufferedAtlas P Ep) (amplitude : ℝ) (ha : 0 < amplitude)
    (b : Fin B.count) (p₀ : P) (u : ProbeParameters r) : M → V :=
  let p := actualRepairParameterMap (tensorChartFamilyOfAtlas B) b p₀
    (round4PairedParameterReindex r u)
  fun x => family.physicalPairMap c hc delta tau length
    (passiveOriginalSmallParameter B amplitude ha b p₀ p) (p,x)

theorem centeredPhysicalPairMap_fderiv
    (family : GeneralLegalWaveRawFamily F hF waves weight)
    (c : ℝ) (hc : c ∈ Icc (1/2:ℝ) 1) (delta tau : ℝ) (length : ℕ)
    (B : BufferedAtlas P Ep) (amplitude : ℝ) (ha : 0 < amplitude)
    (hbuffer : B.buffer ≤ amplitude/
      (‖(EuclideanSpace.equiv (Fin (Fintype.card (Fin r × Bool))) ℝ).toContinuousLinearMap‖+1))
    (b : Fin B.count) (p₀ : P) (hp₀ : p₀ ∈ B.inner b)
    (u : ProbeParameters r)
    (hu : ‖u‖ < actualRepairParameterRadius (tensorChartFamilyOfAtlas B)) (x : M) :
    fderiv ℝ (fun v => family.centeredPhysicalPairMap c hc delta tau length B amplitude ha b p₀ v x) u =
      fderiv ℝ (fun v => family.groupedPairMap c hc delta tau length v x) u := by
  have he := family.physicalPairMap_centered_original_germ c hc delta tau length
    B amplitude ha hbuffer b p₀ hp₀ u hu
  have hv : (fun v => family.centeredPhysicalPairMap c hc delta tau length B amplitude ha b p₀ v x) =ᶠ[𝓝 u]
      (fun v => family.groupedPairMap c hc delta tau length v x) :=
    he.mono (fun _ hv => congrFun hv x)
  exact hv.fderiv_eq

theorem centeredPhysicalPairMap_hessian_fderiv
    (family : GeneralLegalWaveRawFamily F hF waves weight)
    (c : ℝ) (hc : c ∈ Icc (1/2:ℝ) 1) (delta tau : ℝ) (length : ℕ)
    (B : BufferedAtlas P Ep) (amplitude : ℝ) (ha : 0 < amplitude)
    (hbuffer : B.buffer ≤ amplitude/
      (‖(EuclideanSpace.equiv (Fin (Fintype.card (Fin r × Bool))) ℝ).toContinuousLinearMap‖+1))
    (b : Fin B.count) (p₀ : P) (hp₀ : p₀ ∈ B.inner b)
    (u : ProbeParameters r)
    (hu : ‖u‖ < actualRepairParameterRadius (tensorChartFamilyOfAtlas B))
    (chart : D → M) (y : D) :
    fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ
        (family.centeredPhysicalPairMap c hc delta tau length B amplitude ha b p₀ v ∘ chart)) y) u =
      fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ
        (family.groupedPairMap c hc delta tau length v ∘ chart)) y) u := by
  have he := family.physicalPairMap_centered_original_germ c hc delta tau length
    B amplitude ha hbuffer b p₀ hp₀ u hu
  have hh : (fun v => fderiv ℝ (fderiv ℝ
        (family.centeredPhysicalPairMap c hc delta tau length B amplitude ha b p₀ v ∘ chart)) y) =ᶠ[𝓝 u]
      (fun v => fderiv ℝ (fderiv ℝ
        (family.groupedPairMap c hc delta tau length v ∘ chart)) y) := by
    filter_upwards [he] with v hv
    exact congrArg (fun f : M → V => fderiv ℝ (fderiv ℝ (f ∘ chart)) y) hv
  exact hh.fderiv_eq

end GeneralLegalWaveRawFamily
theorem exists_generalLegalWave_physical_responses
    (F : M → V) (hF : ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,V) ∞ F)
    (hImm : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,D) 𝓘(ℝ,V) F x))
    (waves : Fin r → OpenSupportedLegalWave (n := m+1) F hF)
    (weight : Fin r → ℝ) (hweight : ∀ l, 0 < weight l)
    (atlas : BufferedAtlas M D) (hAtlas : IsSmoothBufferedAtlas atlas)
    (Omega : Fin atlas.count → Set D)
    (hcompact : ∀ j, IsCompact (Omega j))
    (htarget : ∀ j, Omega j ⊆ (atlas.chart j).target)
    (B : BufferedAtlas P Ep) (amplitude : ℝ) (ha : 0 < amplitude)
    (hbuffer : B.buffer ≤ amplitude/
      (‖(EuclideanSpace.equiv (Fin (Fintype.card (Fin r × Bool))) ℝ).toContinuousLinearMap‖+1)) :
    ∃ family : GeneralLegalWaveRawFamily F hF waves weight,
    ∀ length : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ modulus : ℝ → ℝ,
      (∀ t, 0 ≤ modulus t) ∧ Tendsto modulus (𝓝[>] 0) (𝓝 0) ∧
      (∀ (c : ℝ) (hc : c ∈ Icc (1/2:ℝ) 1) (t : ℝ), 0 < t → t ≤ 1 →
        ∀ (b : Fin B.count) (p₀ : P), p₀ ∈ B.inner b →
        ∀ (x : M) (u : ProbeParameters r),
        ‖u‖ < actualRepairParameterRadius (tensorChartFamilyOfAtlas B) →
        ∀ (k : Fin r) (sine : Bool),
        ‖fderiv ℝ (fun v => family.centeredPhysicalPairMap c hc (t^(10:ℕ)) (t^((6:ℝ)/5)) length B amplitude ha b p₀ v x)
            u (Pi.single (k,sine) 1) -
          (-(t^((56:ℝ)/5))*(weight k^2)⁻¹ *
            probeTrig sine (weight k*(waves k).phase x/t^((6:ℝ)/5))) • (waves k).value x‖ ≤
          t^((56:ℝ)/5) * (C * |t|^((1:ℝ)/10))) ∧
      (∀ (c : ℝ) (hc : c ∈ Icc (1/2:ℝ) 1) (t : ℝ), 0 < t → t ≤ 1 →
        ∀ (b : Fin B.count) (p₀ : P), p₀ ∈ B.inner b →
        ∀ j y, y ∈ Omega j → ∀ (u : ProbeParameters r),
        ‖u‖ < actualRepairParameterRadius (tensorChartFamilyOfAtlas B) →
        ∀ (k : Fin r) (sine : Bool),
        ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ
            (family.centeredPhysicalPairMap c hc (t^(10:ℕ)) (t^((6:ℝ)/5)) length B amplitude ha b p₀ v ∘ (atlas.chart j).symm))
            y) u (Pi.single (k,sine) 1) -
          (t^((44:ℝ)/5)*probeTrig sine
            (weight k*(waves k).phase ((atlas.chart j).symm y)/t^((6:ℝ)/5))) •
            phaseRankOneHessian ((waves k).phase ∘ (atlas.chart j).symm)
              ((waves k).value ∘ (atlas.chart j).symm) y‖ ≤
          t^((44:ℝ)/5) * modulus t) := by
  obtain ⟨family,hfamily⟩ := exists_generalLegalWave_paper_responses
    F hF hImm waves weight hweight atlas hAtlas Omega hcompact htarget
  refine ⟨family,?_⟩
  intro length
  obtain ⟨C,hC,modulus,hnonneg,hlimit,hvalue,hhessian⟩ := hfamily length
  refine ⟨C,hC,modulus,hnonneg,hlimit,?_,?_⟩
  · intro c hc t ht ht1 b p₀ hp₀ x u hu k sine
    rw [family.centeredPhysicalPairMap_fderiv c hc _ _ length
      B amplitude ha hbuffer b p₀ hp₀ u hu x]
    exact hvalue c hc t ht ht1 x u k sine
  · intro c hc t ht ht1 b p₀ hp₀ j y hy u hu k sine
    rw [family.centeredPhysicalPairMap_hessian_fderiv c hc _ _ length
      B amplitude ha hbuffer b p₀ hp₀ u hu (atlas.chart j).symm y]
    exact hhessian c hc t ht ht1 j y hy u k sine

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.GeneralLegalWaveRawFamily.centeredPhysicalPairMap_fderiv
#print axioms GlobalEmbedding.Continuation.GeneralLegalWaveRawFamily.centeredPhysicalPairMap_hessian_fderiv

#print axioms GlobalEmbedding.Continuation.exists_generalLegalWave_physical_responses
