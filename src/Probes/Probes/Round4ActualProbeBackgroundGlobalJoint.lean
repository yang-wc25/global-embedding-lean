import Probes.Round4ActualProbeRestrictedParameterLift
import Probes.Round4ActualProbeGlobalWaveProducer

/-! Joint regularity of the SAME complete global background wave on a genuine
open parameter neighborhood. Positivity is needed only there, on the original
relative cutoff support. Parameter-restricted charts are proved equal to the
original whole-field solver on this domain; no output regularity is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation
variable {P E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
variable (F : Ep → M → EuclideanSpace ℝ (Fin N))
  (hF : ∀ b, ContMDiff I 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F b))
  (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)

theorem round4_actual_background_global_joint
    (Su : Set P) (hSu : IsOpen Su)
    (input : P → (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ)
    (W : Set (Ep × M)) (_hW : IsOpen W) (primary : Λ → Set (Ep × M))
    (_hPrimary : ∀ ν, IsOpen (primary ν))
    (_hPrimarySupport : ∀ ν, incrementsGlobalRelativeSupport W (g.cutoff ν) ⊆ primary ν)
    (_hSourceW : ∀ ν β, (g.chart ν β).source ⊆ W ∩ primary ν)
    (_hChart : ∀ ν β, ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, Ep × (EuclideanSpace ℝ (Fin (m + 1)))) ∞
      (g.chart ν β) (g.chart ν β).source)
    (_hChartInv : ∀ ν β, ContMDiffOn 𝓘(ℝ, Ep × (EuclideanSpace ℝ (Fin (m + 1)))) 
      ((𝓘(ℝ, Ep)).prod I) ∞ (g.chart ν β).symm (g.chart ν β).target)
    (_hInverse : ∀ ν β z, z ∈ (g.chart ν β).target →
      (g.chart ν β).symm z = (z.1, g.inverse ν β z.1 z.2))
    (_hCombinedSupport : ∀ ν β,
      incrementsGlobalRelativeSupport W (fun z ↦ g.eta ν β z * g.cutoff ν z) ⊆
        (g.chart ν β).source)
    (_hPhase : ∀ ν, ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,ℝ) ∞ (g.phase ν) W)
    (_hCut : ∀ ν, ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, ℝ) ∞
      (g.cutoff ν) (W ∩ primary ν))
    (_hNormal : ∀ ν, ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, (EuclideanSpace ℝ (Fin N))) ∞
      (g.normal ν) (W ∩ primary ν))
    (_hArgument : ∀ ν, ContMDiffOn ((𝓘(ℝ,P×Ep)).prod I) 𝓘(ℝ,ℝ) ∞
      (fun z : (P×Ep)×M => g.linearArgument ν z.1.2 z.2 (input z.1.1 z.1.2 z.2))
      ((((fun z : (P×Ep)×M => z.1.1) ⁻¹' Su) ∩
        ((fun z : (P×Ep)×M => (z.1.2,z.2)) ⁻¹' W)) ∩
        ((fun z : (P×Ep)×M => (z.1.2,z.2)) ⁻¹' primary ν)))
    (_hEta : ∀ ν β, ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, ℝ) ∞ (g.eta ν β) W)
    (_hPositive : ∀ u ∈ Su, ∀ ν z, z ∈ incrementsGlobalRelativeSupport W (g.cutoff ν) →
      0 < g.linearArgument ν z.1 z.2 (input u z.1 z.2))
    (_hG : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      freeGramRightInverse (fderiv ℝ (F z.1 ∘ g.inverse ν β z.1) z.2))
      (g.chart ν β).target)
    (_hJ : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      (normalSpace (I := I) (F z.1) (g.inverse ν β z.1 z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (g.inverse ν β z.1) z.2))
      (g.chart ν β).target)
    (_hT0 : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      incrementsModeTransverseValue (F z.1) (g.inverse ν β z.1) z.2) (g.chart ν β).target)
    (_hA : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (g.inverse ν β z.1) z.2)
      (g.chart ν β).target)
    (_hB : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (g.inverse ν β z.1) z.2)
      (g.chart ν β).target)
    (_hSecond : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      fun i : Fin (m + 1) ↦
      (incrementsModeSecondForm (F z.1) (hF z.1) (g.inverse ν β z.1) z.2 0 i :
        (EuclideanSpace ℝ (Fin N))))
      (g.chart ν β).target) :
    let U : Set ((P×Ep)×M) :=
      ((fun z : (P×Ep)×M => z.1.1) ⁻¹' Su) ∩
      ((fun z : (P×Ep)×M => (z.1.2,z.2)) ⁻¹' W)
    (∀ ch ν β, ContMDiffOn ((𝓘(ℝ,P×Ep)).prod I) 𝓘(ℝ,V) ∞
      (fun z : (P×Ep)×M => incrementsGlobalPrimaryExtension F hF g (input z.1.1)
        length tau ch ν β (z.1.2,z.2)) U) ∧
    (∀ ch ν, ContMDiffOn ((𝓘(ℝ,P×Ep)).prod I) 𝓘(ℝ,V) ∞
      (fun z : (P×Ep)×M => incrementsGlobalPrimaryAmplitude F hF g (input z.1.1)
        length tau ch ν (z.1.2,z.2)) U) ∧
    ContMDiffOn ((𝓘(ℝ,P×Ep)).prod I) 𝓘(ℝ,V) ∞
      (fun z : (P×Ep)×M => incrementsGlobalPrimaryWave F hF g (input z.1.1)
        length tau (z.1.2,z.2)) U := by
  intro U
  let pi : (P×Ep)×M → Ep×M := fun z => (z.1.2,z.2)
  let gL : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β)
      (fun t : P×Ep => F t.2) := round4PrimaryRestrictedParameterFamily Su hSu F g
  let primaryL := fun nu => pi ⁻¹' primary nu
  have hp := round4_primary_parameter_projection_smooth (P := P) (Ep := Ep) (I := I) (M := M)
  have hU : IsOpen U := (hSu.preimage continuous_fst.fst).inter (_hW.preimage hp.continuous)
  have hrel (f : Ep×M → ℝ) :
      incrementsGlobalRelativeSupport U (fun z => f (pi z)) ⊆
        pi ⁻¹' incrementsGlobalRelativeSupport W f := by
    rw [round4_relative_support_open U hU,round4_relative_support_open W _hW]
    intro z hz
    exact ⟨hz.1.2,tsupport_comp_subset_preimage f hp.continuous hz.2⟩
  have hrelU (f : (P×Ep)×M → ℝ) : incrementsGlobalRelativeSupport U f ⊆ U := by
    rw [round4_relative_support_open U hU]
    exact inter_subset_left
  have hs (nu : Λ) (beta : Β) (z : (P×Ep)×M) (hz : z ∈ (gL.chart nu beta).source) :
      z ∈ U ∩ primaryL nu := by
    have hh := (round4_restricted_chart_source Su hSu (g.chart nu beta) z).mp hz
    exact ⟨⟨hh.2,(_hSourceW nu beta hh.1).1⟩,(_hSourceW nu beta hh.1).2⟩
  have hc (nu : Λ) (beta : Β) := round4_primary_parameter_chart_smooth
    (P := P) (g.chart nu beta) (_hChart nu beta) (_hChartInv nu beta)
  have hct (nu : Λ) (beta : Β) : ContMDiffOn ((𝓘(ℝ,P×Ep)).prod I) 𝓘(ℝ,(P×Ep)×D) ∞
      (gL.chart nu beta) (gL.chart nu beta).source :=
    (hc nu beta).1.mono (fun z hz => hz.1)
  have hci (nu : Λ) (beta : Β) : ContMDiffOn 𝓘(ℝ,(P×Ep)×D) ((𝓘(ℝ,P×Ep)).prod I) ∞
      (gL.chart nu beta).symm (gL.chart nu beta).target :=
    (hc nu beta).2.mono (fun z hz => hz.1)
  have hinv (nu : Λ) (beta : Β) (z : (P×Ep)×D) (hz : z ∈ (gL.chart nu beta).target) :
      (gL.chart nu beta).symm z = (z.1,gL.inverse nu beta z.1 z.2) := by
    have hb := ((round4_restricted_chart_target Su hSu (g.chart nu beta) z).mp hz).1
    change ((z.1.1,((g.chart nu beta).symm (z.1.2,z.2)).1),
      ((g.chart nu beta).symm (z.1.2,z.2)).2) = _
    rw [_hInverse nu beta _ hb]
    rfl
  have hproj : ContDiff ℝ ∞ (fun z : (P×Ep)×D => (z.1.2,z.2)) :=
    contDiff_fst.snd.prodMk contDiff_snd
  have ht (nu : Λ) (beta : Β) : MapsTo (fun z : (P×Ep)×D => (z.1.2,z.2))
      (gL.chart nu beta).target (g.chart nu beta).target :=
    fun z hz => ((round4_restricted_chart_target Su hSu (g.chart nu beta) z).mp hz).1
  have hreg := round4_actual_global_primary_wave_regular (I := I) (m := m) (N := N)
    (Λ := Λ) (Β := Β) (fun t : P×Ep => F t.2)
    (fun t : P×Ep => hF t.2) gL
  have hreg0 := hreg (fun (t : P×Ep) (x : M) => input t.1 t.2 x) length tau U hU primaryL
  have hreg1 := hreg0 (fun nu => by exact (_hPrimary nu).preimage hp.continuous)
  have hreg2 := hreg1 (fun nu z hz => by exact _hPrimarySupport nu (hrel (g.cutoff nu) hz))
  have hreg3 := hreg2 hs hct hci hinv
  have hreg := hreg3
    (by
      intro nu beta z hz
      apply (round4_restricted_chart_source Su hSu (g.chart nu beta) z).mpr
      exact ⟨_hCombinedSupport nu beta (hrel (fun w => g.eta nu beta w*g.cutoff nu w) hz),
        (hrelU _ hz).1⟩)
    (fun nu => (_hPhase nu).comp hp.contMDiffOn (fun z hz => hz.2))
    (fun nu => by exact (_hCut nu).comp hp.contMDiffOn (fun z hz => ⟨hz.1.2,hz.2⟩))
    (fun nu => by exact (_hNormal nu).comp hp.contMDiffOn (fun z hz => ⟨hz.1.2,hz.2⟩))
    (by exact _hArgument)
    (fun nu beta => by exact (_hEta nu beta).comp hp.contMDiffOn (fun z hz => hz.2))
    (fun nu z hz => _hPositive z.1.1 (hrelU _ hz).1 nu (pi z) (hrel (g.cutoff nu) hz))
    (fun nu beta => by
      dsimp only [gL,round4PrimaryRestrictedParameterFamily]
      simpa only [Function.comp_def,gL,round4PrimaryRestrictedParameterFamily] using (_hG nu beta).comp hproj.contDiffOn (ht nu beta))
    (fun nu beta => by
      dsimp only [gL,round4PrimaryRestrictedParameterFamily]
      simpa only [Function.comp_def,gL,round4PrimaryRestrictedParameterFamily] using (_hJ nu beta).comp hproj.contDiffOn (ht nu beta))
    (fun nu beta => by
      dsimp only [gL,round4PrimaryRestrictedParameterFamily]
      simpa only [Function.comp_def,gL,round4PrimaryRestrictedParameterFamily] using (_hT0 nu beta).comp hproj.contDiffOn (ht nu beta))
    (fun nu beta => by
      dsimp only [gL,round4PrimaryRestrictedParameterFamily]
      simpa only [Function.comp_def,gL,round4PrimaryRestrictedParameterFamily] using (_hA nu beta).comp hproj.contDiffOn (ht nu beta))
    (fun nu beta => by
      dsimp only [gL,round4PrimaryRestrictedParameterFamily]
      simpa only [Function.comp_def,gL,round4PrimaryRestrictedParameterFamily] using (_hB nu beta).comp hproj.contDiffOn (ht nu beta))
    (fun nu beta => by
      dsimp only [gL,round4PrimaryRestrictedParameterFamily]
      simpa only [Function.comp_def,gL,round4PrimaryRestrictedParameterFamily] using (_hSecond nu beta).comp hproj.contDiffOn (ht nu beta))
  have hext (ch : Bool) (nu : Λ) (beta : Β) : ContMDiffOn ((𝓘(ℝ,P×Ep)).prod I) 𝓘(ℝ,V) ∞
      (fun z : (P×Ep)×M => incrementsGlobalPrimaryExtension F hF g (input z.1.1)
        length tau ch nu beta (z.1.2,z.2)) U := by
    have hh : ContMDiffOn ((𝓘(ℝ,P×Ep)).prod I) 𝓘(ℝ,V) ∞
      (incrementsGlobalPrimaryExtension (fun t : P×Ep => F t.2) (fun t => hF t.2)
        gL (fun t x => input t.1 t.2 x) length tau ch nu beta) U := by
      exact hreg.1 ch nu beta
    exact hh.congr (fun z hz =>
      (round4_restricted_parameter_extension Su hSu F hF g input length tau ch nu beta
        z.1.1 hz.1 z.1.2 z.2).symm)
  have hamp (ch : Bool) (nu : Λ) : ContMDiffOn ((𝓘(ℝ,P×Ep)).prod I) 𝓘(ℝ,V) ∞
      (fun z : (P×Ep)×M => incrementsGlobalPrimaryAmplitude F hF g (input z.1.1)
        length tau ch nu (z.1.2,z.2)) U := by
    intro z hz
    apply ContMDiffWithinAt.sum
    intro beta hb
    exact hext ch nu beta z hz
  refine ⟨hext,hamp,?_⟩
  intro z hz
  apply ContMDiffWithinAt.sum
  intro nu hnu
  have hph := ((_hPhase nu).comp hp.contMDiffOn (fun z hz => hz.2)) z hz
  exact ((Real.contDiff_cos.comp_contMDiffWithinAt
    (hph.div_const tau)).smul (hamp true nu z hz)).sub
      ((Real.contDiff_sin.comp_contMDiffWithinAt
        (hph.div_const tau)).smul (hamp false nu z hz))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_actual_background_global_joint
