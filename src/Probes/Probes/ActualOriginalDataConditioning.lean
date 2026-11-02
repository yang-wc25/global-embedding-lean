import Probes.ActualOriginalConditionedFamily
import Probes.ActualIncrementOriginalPrimitiveBinding
import Probes.ActualIncrementOriginalOpenImmersion

/-!
# Original Data produces conditioning of its actual finite host packet

Original joint smoothness, immersion and the SAME primary Good phases supply
every qualitative input of the compact conditioning construction. The actual
compact cutoff carriers come from the produced finite refinement. No chosen
margin, inverse estimate, Riemannian bundle, or higher-jet budget is assumed.
The common reserves and restricted host family precede every later order.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × Es
local notation "𝓙" => 𝓘(ℝ,Es)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
variable {Β : Type*} [Fintype Β]

theorem actual_original_data_host_family_conditioning
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (host : Fin Data.primaryCount → Β → Fin Data.atlas.count)
    (b : Fin Data.primaryCount → Β → OpenPartialHomeomorph X X)
    (e : Fin Data.primaryCount → Β → Ep → OpenPartialHomeomorph M Es)
    (hdata : ∀ nu beta, ActualOriginalHostSliceData (Data.atlas.chart (host nu beta)) (b nu beta)
      (fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) (e nu beta))
    (eta : Fin Data.primaryCount → Β → Ep × M → ℝ)
    (hCompact : ∀ nu beta, IsCompact (tsupport (eta nu beta)))
    (hSupport : ∀ nu beta, tsupport (eta nu beta) ⊆
      (actualHostAdaptedChart (Data.atlas.chart (host nu beta)) (b nu beta)).source)
    (hsource : ∀ nu beta, (b nu beta).source ⊆ actualOriginalNativeOpen Data (host nu beta,i.2))
    (hactive : ∀ nu beta w,
      w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu beta)) (b nu beta)).source →
      ((Data.parameterChart i.2).symm w.1,w.2) ∈
        Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data) :
    let F := actualOriginalOpenParameterSlice Data i
    let hF := actualOriginalOpenParameterSlice_contMDiff Data hd hs i
    ∃ (cF cT : ℝ) (b' : Fin Data.primaryCount → Β → OpenPartialHomeomorph X X)
        (e' : Fin Data.primaryCount → Β → Ep → OpenPartialHomeomorph M Es),
      0 < cF ∧ 0 < cT ∧ ∀ nu beta,
        (b' nu beta).source ⊆ (b nu beta).source ∧
        (b' nu beta).target ⊆ (b nu beta).target ∧
        (b' nu beta : X → X) = b nu beta ∧
        ((b' nu beta).symm : X → X) = (b nu beta).symm ∧
        ActualOriginalHostSliceData (Data.atlas.chart (host nu beta)) (b' nu beta)
          (fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) (e' nu beta) ∧
        tsupport (eta nu beta) ⊆
          (actualHostAdaptedChart (Data.atlas.chart (host nu beta)) (b' nu beta)).source ∧
        (actualHostAdaptedChart (Data.atlas.chart (host nu beta)) (b' nu beta)).source ⊆
          (actualHostAdaptedChart (Data.atlas.chart (host nu beta)) (b nu beta)).source ∧
        (∀ p, ((e' nu beta p).symm : Es → M) = (e nu beta p).symm) ∧
        (∀ z ∈ (b' nu beta).target, ∀ v : Es,
          cF*‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e' nu beta z.1).symm) z.2 v‖^2) ∧
        ∀ z ∈ (b' nu beta).target, ∀ v : Tdata,
          cT*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame
            (F z.1) (hF z.1) (e' nu beta z.1).symm z.2 v‖^2 := by
  intro F hF
  let W := fun a : Fin Data.primaryCount × Β =>
    (actualHostAdaptedChart (Data.atlas.chart (host a.1 a.2)) (b a.1 a.2)).source
  have hParam (a : Fin Data.primaryCount × Β) (z : Ep × M) (hz : z ∈ W a) :
      z.1 ∈ (Data.parameterChart i.2).target := by
    let q := actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart (host a.1 a.2))
    have hn := hsource a.1 a.2 hz.2
    have heq := congrArg Prod.fst ((parameterTensorModelEquiv (m+1) d).symm_apply_apply (q z))
    change incrementsOriginalParameterPoint (parameterTensorModelEquiv (m+1) d (q z)) = z.1 at heq
    have ht := hn.1.2
    change incrementsOriginalParameterPoint (parameterTensorModelEquiv (m+1) d (q z)) ∈
      (Data.parameterChart i.2).target at ht
    rwa [heq] at ht
  have hFjoint (a : Fin Data.primaryCount × Β) :
      ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞ (Function.uncurry F) (W a) := by
    have hh := actual_original_parameter_pullback_smooth Data hd i.2 Data.F
      (incrementsOriginalParameterRegion Data) hs.F_joint (W a) (hParam a)
      (fun z hz => (hactive a.1 a.2 z hz).2)
    apply hh.congr
    intro z hz
    change actualOriginalOpenParameterSlice Data i z.1 z.2 = _
    rw [actualOriginalOpenParameterSlice_eq Data i z.1 (hactive a.1 a.2 z hz).2.1]
    rfl
  have hpsi (a : Fin Data.primaryCount × Β) :
      ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞
        (fun z : Ep × M => Data.phase a.1 ((Data.parameterChart i.2).symm z.1,z.2)) (W a) :=
    actual_original_parameter_pullback_smooth Data hd i.2 (Data.phase a.1)
      (Data.primaryDomain a.1 ∩ incrementsOriginalParameterRegion Data) (hs.phase_joint a.1)
      (W a) (hParam a) (hactive a.1 a.2)
  have hInj (a : Fin Data.primaryCount × Β) (z : Ep × M) (hz : z ∈ W a) :
      Function.Injective (mfderiv 𝓙 𝓘(ℝ,V) (F z.1) z.2) := by
    change Function.Injective (mfderiv 𝓙 𝓘(ℝ,V) (actualOriginalOpenParameterSlice Data i z.1) z.2)
    rw [actualOriginalOpenParameterSlice_eq Data i z.1 (hactive a.1 a.2 z hz).2.1]
    exact hImm.immersion _ (hactive a.1 a.2 z hz).2.1 z.2
  have hGood (a : Fin Data.primaryCount × Β) (z : Ep × M) (hz : z ∈ W a) :
      GoodCovector (F z.1) (hF z.1) z.2
        ((tangentSpaceCastModel 𝓘(ℝ,ℝ) (Data.phase a.1 ((Data.parameterChart i.2).symm z.1,z.2))).toContinuousLinearMap.comp
          (mfderiv 𝓙 𝓘(ℝ,ℝ) (fun x => Data.phase a.1 ((Data.parameterChart i.2).symm z.1,x)) z.2)) := by
    have htransport (f : M → V) (hf : ContMDiff 𝓙 𝓘(ℝ,V) ∞ f)
        (heq : f = fun x => Data.F ((Data.parameterChart i.2).symm z.1,x)) :
        GoodCovector f hf z.2
          ((tangentSpaceCastModel 𝓘(ℝ,ℝ) (Data.phase a.1 ((Data.parameterChart i.2).symm z.1,z.2))).toContinuousLinearMap.comp
            (mfderiv 𝓙 𝓘(ℝ,ℝ) (fun x => Data.phase a.1 ((Data.parameterChart i.2).symm z.1,x)) z.2)) := by
      subst f
      exact hp.primary_good a.1 _ (hactive a.1 a.2 z hz)
    exact htransport (F z.1) (hF z.1)
      (actualOriginalOpenParameterSlice_eq Data i z.1 (hactive a.1 a.2 z hz).2.1)
  obtain ⟨cF,cT,b',e',hcF,hcT,hout⟩ := actual_original_host_family_conditioning
    (ι := Fin Data.primaryCount × Β) F hF
    (fun a => Data.atlas.chart (host a.1 a.2)) (fun a => hd.atlas_smooth.chart_mem (host a.1 a.2))
    (fun a => b a.1 a.2) (fun a z => Data.phase a.1 ((Data.parameterChart i.2).symm z.1,z.2))
    (fun a => e a.1 a.2) (fun a => hdata a.1 a.2) W
    (fun a => (actualHostAdaptedChart (Data.atlas.chart (host a.1 a.2)) (b a.1 a.2)).open_source)
    hFjoint hpsi (fun _ => subset_rfl) (fun a => eta a.1 a.2) (fun a => hCompact a.1 a.2)
    (fun a => hSupport a.1 a.2) hInj hGood
  exact ⟨cF,cT,(fun nu beta => b' (nu,beta)),(fun nu beta => e' (nu,beta)),hcF,hcT,
    fun nu beta => hout (nu,beta)⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_original_data_host_family_conditioning
