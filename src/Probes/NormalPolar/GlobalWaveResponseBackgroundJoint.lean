import Probes.Round4ActualProbeBackgroundGlobalJoint
import Smoothing.ParameterRound2MeanPrimitives

/-! The true background wave is jointly smooth from the original local
phase regularity. A phase is needed only on its actual primary support;
no global smoothness of an arbitrary phase extension is imposed. The
reconstructed amplitudes are unchanged when proving their joint regularity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Continuation
variable {P E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)

theorem globalWave_background_global_joint_from_primitive
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I:=I) (m:=m) (N:=N) (Λ:=Λ) (Β:=Β) F)
    (input : P → (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (inputRef : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (Su : Set P) (hSu : IsOpen Su) (W : Set (Ep×M)) (primary : Λ → Set (Ep×M))
    (base : ParameterRound2GlobalMeanPrimitives F hF g inputRef W primary)
    (hArgument : ∀ nu, ContMDiffOn ((𝓘(ℝ,P×Ep)).prod I) 𝓘(ℝ,ℝ) ∞
      (fun z : (P×Ep)×M => g.linearArgument nu z.1.2 z.2 (input z.1.1 z.1.2 z.2))
      ((((fun z : (P×Ep)×M => z.1.1) ⁻¹' Su) ∩
        ((fun z : (P×Ep)×M => (z.1.2,z.2)) ⁻¹' W)) ∩
        ((fun z : (P×Ep)×M => (z.1.2,z.2)) ⁻¹' primary nu)))
    (hPositive : ∀ v ∈ Su, ∀ nu z, z ∈ incrementsGlobalRelativeSupport W (g.cutoff nu) →
      0 < g.linearArgument nu z.1 z.2 (input v z.1 z.2))
    (length : ℕ) (tau : ℝ) :
    ContMDiffOn ((𝓘(ℝ,P×Ep)).prod I) 𝓘(ℝ,V) ∞
      (fun z : (P×Ep)×M => incrementsGlobalPrimaryWave F hF g (input z.1.1) length tau (z.1.2,z.2))
      (((fun z : (P×Ep)×M => z.1.1) ⁻¹' Su) ∩
        ((fun z : (P×Ep)×M => (z.1.2,z.2)) ⁻¹' W)) := by
  let U : Set ((P×Ep)×M) := ((fun z : (P×Ep)×M => z.1.1) ⁻¹' Su) ∩
    ((fun z : (P×Ep)×M => (z.1.2,z.2)) ⁻¹' W)
  let pi : (P×Ep)×M → Ep×M := fun z => (z.1.2,z.2)
  have hp := round4_primary_parameter_projection_smooth (P:=P) (Ep:=Ep) (I:=I) (M:=M)
  have hU : IsOpen U := (hSu.preimage continuous_fst.fst).inter (base.hW.preimage hp.continuous)
  let g0 : IncrementsGlobalPrimaryFamily (I:=I) (m:=m) (N:=N) (Λ:=Λ) (Β:=Β) F :=
    {g with phase := fun _ _ => 0}
  have hreg0 := round4_actual_background_global_joint F hF g0 Su hSu input length tau
    W base.hW primary base.hPrimary base.hPrimarySupport base.hSourceW base.hChart base.hChartInv
    base.hInverse base.hCombinedSupport (fun _ => contMDiffOn_const) base.hCut base.hNormal
    hArgument base.hEta hPositive base.hG base.hJ base.hT0 base.hA base.hB base.hSecond
  have hamp (ch : Bool) (nu : Λ) : ContMDiffOn ((𝓘(ℝ,P×Ep)).prod I) 𝓘(ℝ,V) ∞
      (fun z : (P×Ep)×M => incrementsGlobalPrimaryAmplitude F hF g (input z.1.1)
        length tau ch nu (pi z)) U := (hreg0.2.1 ch nu)
  have hArgSlice (v : P) (hv : v ∈ Su) (nu : Λ) :
      ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,ℝ) ∞
        (fun z : Ep×M => g.linearArgument nu z.1 z.2 (input v z.1 z.2)) (W ∩ primary nu) := by
    have hm : ContMDiff ((𝓘(ℝ,Ep)).prod I) ((𝓘(ℝ,P×Ep)).prod I) ∞
        (fun z : Ep×M => ((v,z.1),z.2)) :=
      (((show ContDiff ℝ ∞ (fun b : Ep => (v,b)) from
        contDiff_const.prodMk contDiff_id).contMDiff).comp contMDiff_fst).prodMk contMDiff_snd
    exact (hArgument nu).comp hm.contMDiffOn (fun z hz => ⟨⟨hv,hz.1⟩,hz.2⟩)
  have hr (v : P) (hv : v ∈ Su) := actual_global_primary_extension_regular F hF g (input v)
    length tau W base.hW primary base.hPrimary base.hPrimarySupport base.hSourceW base.hChart
    base.hChartInv base.hInverse base.hCombinedSupport base.hCut base.hNormal (hArgSlice v hv)
    base.hEta (hPositive v hv) base.hG base.hJ base.hT0 base.hA base.hB base.hSecond
  have hzero (v : P) (hv : v ∈ Su) (ch : Bool) (nu : Λ) (z : Ep×M)
      (hz : z ∈ W) (hn : z ∉ tsupport (g.cutoff nu)) :
      incrementsGlobalPrimaryAmplitude F hF g (input v) length tau ch nu z = 0 := by
    apply Finset.sum_eq_zero
    intro beta _
    have hnot : z ∉ incrementsGlobalRelativeSupport W (fun w => g.eta nu beta w*g.cutoff nu w) := by
      rw [parameterRound2_global_relativeSupport_eq W base.hW]
      exact fun h => hn (tsupport_mul_subset_right h.2)
    have hsupport : tsupport (fun w : W =>
        incrementsGlobalPrimaryExtension F hF g (input v) length tau ch nu beta w) ⊆
        Subtype.val ⁻¹' incrementsGlobalRelativeSupport W (fun w => g.eta nu beta w*g.cutoff nu w) := by
      cases ch
      · exact (hr v hv nu beta).2.2.2.2.2
      · exact (hr v hv nu beta).2.2.2.2.1
    exact image_eq_zero_of_notMem_tsupport (f := fun w : W =>
      incrementsGlobalPrimaryExtension F hF g (input v) length tau ch nu beta w)
      (x := ⟨z,hz⟩) (fun h => hnot (hsupport h))
  intro z hz
  apply ContMDiffWithinAt.sum
  intro nu _
  by_cases hcut : pi z ∈ tsupport (g.cutoff nu)
  · have hrel : pi z ∈ incrementsGlobalRelativeSupport W (g.cutoff nu) := by
      rw [parameterRound2_global_relativeSupport_eq W base.hW]
      exact ⟨hz.2,hcut⟩
    have hph := ((base.hPhase nu).contMDiffAt
      ((base.hW.inter (base.hPrimary nu)).mem_nhds ⟨hz.2,base.hPrimarySupport nu hrel⟩)).comp z hp.contMDiffAt
    exact ((Real.contDiff_cos.comp_contMDiffWithinAt (hph.div_const tau).contMDiffWithinAt).smul
      (hamp true nu z hz)).sub
      ((Real.contDiff_sin.comp_contMDiffWithinAt (hph.div_const tau).contMDiffWithinAt).smul
        (hamp false nu z hz))
  · apply ContMDiffAt.contMDiffWithinAt
    apply (contMDiffAt_const (c := (0 : V))).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hz,
      hp.continuous.continuousAt.tendsto.eventually
        ((isClosed_tsupport (g.cutoff nu)).isOpen_compl.mem_nhds hcut)] with w hw hcw
    change Real.cos (g.phase nu (pi w)/tau) •
      incrementsGlobalPrimaryAmplitude F hF g (input w.1.1) length tau true nu (pi w)-
      Real.sin (g.phase nu (pi w)/tau) •
      incrementsGlobalPrimaryAmplitude F hF g (input w.1.1) length tau false nu (pi w) = 0
    simp only [hzero w.1.1 hw.1 true nu (pi w) hw.2 hcw,
      hzero w.1.1 hw.1 false nu (pi w) hw.2 hcw,smul_zero,sub_zero]

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.globalWave_background_global_joint_from_primitive
