import NormalPolar.ActualProbeInitialSupplyGroupedAmplitude
import NormalPolar.ActualRepairModelFirstDefectTotalCoordinates

/-!
# The same physical mean on the original parameter manifold

The original combined mean is pulled back through the actual parameter chart.
Its native tensor is the opposite mean of the joint amplitudes that produced
the secondary source. In spatial derivatives the parameter is fixed, so
substituting the whole parameter field before taking joint jets preserves the
native mean exactly. No completed mean identity is assumed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N p r count : ℕ} {M P Λ Β : Type*}
  [TopologicalSpace P] [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β]
  {Pieces : Fin r → Type*} [∀ l, Fintype (Pieces l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "IM" => 𝓘(ℝ,D)

attribute [local irreducible] OpenPartialHomeomorph.symm

set_option backward.isDefEq.respectTransparency true in
theorem actualProbeInitialSupply_grouped_mean_native
    (F : P → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (g : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Λ) (Β := Β) F)
    (label : (Fin r × Bool) ↪ Fin p)
    (c : (l : Fin r) → Pieces l → P → D → M)
    (vf : (l : Fin r) → (s : Pieces l) → (b : P) → (x : D) → normalSpace (I := IM) (F b) (c l s b x))
    (phase : Fin r → P × M → ℝ) (tau delta : ℝ) (backgroundLength probeLength : ℕ)
    (a : (l : Fin r) → Pieces l → OpenPartialHomeomorph (P × M) (P × D))
    (input : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
    (u : P → Fin p → ℝ)
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A)
    (B : Fin count → OpenPartialHomeomorph P Ep)
    (hg : ∀ l b, Round3ParameterChartPreserves (g.chart l b))
    (ha : ∀ l s, Round3ParameterChartPreserves (a l s))
    (i : Fin A.count × Fin count) (z : X)
    (hz : z ∈ (B i.2).target ×ˢ (A.chart i.1).target) :
    let physicalMean := actualProbeInitialGroupedMean F hF g label c vf phase
      tau delta backgroundLength probeLength a input u
    let Fbar := fun t => F ((B i.2).symm t)
    let hFbar := fun t => hF ((B i.2).symm t)
    let gbar := (round3ParameterPrimaryPullback F g (B i.2)).toNative Fbar
    let cbar := fun l s t => c l s ((B i.2).symm t)
    let vfbar := fun l s t => vf l s ((B i.2).symm t)
    let abar := fun l s => round3ParameterChartPullback (B i.2) (a l s)
    let phasebar := fun l z => phase l ((B i.2).symm z.1,z.2)
    let phases := Sum.elim gbar.phase phasebar
    let nativeAmplitude := jointGroupedCombinedAmplitude Fbar hFbar gbar label cbar vfbar
      tau delta backgroundLength probeLength abar (fun t => input ((B i.2).symm t))
      (fun t => u ((B i.2).symm t))
    actualOriginalNativeTargetTensor A B physicalMean i z =
      actualPrimaryOppositeMeanTensor
        (fun l t x => phases l (t,(A.chart i.1).symm x)) tau
        (fun (_ : Λ ⊕ Fin r) (_ : Ep) (_ : Unit) (_ : D) => 1)
        (fun l t (_ : Unit) x => nativeAmplitude false l (t,(A.chart i.1).symm x))
        (fun l t (_ : Unit) x => nativeAmplitude true l (t,(A.chart i.1).symm x)) z := by
  intro physicalMean Fbar hFbar gbar cbar vfbar abar phasebar phases nativeAmplitude
  let amplitude := actualProbeInitialGroupedAmplitude F hF g label c vf tau delta
    backgroundLength probeLength a input u
  have hcoef (ch : Bool) (l : Λ ⊕ Fin r) :
      round4PrescribedNativeCoefficient (I := IM) ch (phases l) tau
        (nativeAmplitude false l) (nativeAmplitude true l) (z.1,(A.chart i.1).symm z.2) =
      round4PrescribedNativeCoefficient (I := IM) ch (Sum.elim g.phase phase l) tau
        (amplitude false l) (amplitude true l) ((B i.2).symm z.1,(A.chart i.1).symm z.2) := by
    have hR := funext (actualProbeInitialSupply_grouped_amplitude_pullback F hF g label c vf
      tau delta backgroundLength probeLength a input u (B i.2) hg ha false l z.1 hz.1)
    have hQ := funext (actualProbeInitialSupply_grouped_amplitude_pullback F hF g label c vf
      tau delta backgroundLength probeLength a input u (B i.2) hg ha true l z.1 hz.1)
    have hp : (fun y => phases l (z.1,y)) =
        fun y => Sum.elim g.phase phase l ((B i.2).symm z.1,y) := by cases l <;> rfl
    have hdR := congrArg (fun f : M → V => mvfderiv IM f ((A.chart i.1).symm z.2)) hR
    have hdQ := congrArg (fun f : M → V => mvfderiv IM f ((A.chart i.1).symm z.2)) hQ
    have hdp := congrArg (fun f : M → ℝ => mvfderiv IM f ((A.chart i.1).symm z.2)) hp
    have hfastR := congrArg₂
      (fun (deriv : TangentSpace IM ((A.chart i.1).symm z.2) →L[ℝ] ℝ) (value : V) =>
        deriv.smulRight (tau⁻¹ • value)) hdp (congrFun hR ((A.chart i.1).symm z.2))
    have hfastQ := congrArg₂
      (fun (deriv : TangentSpace IM ((A.chart i.1).symm z.2) →L[ℝ] ℝ) (value : V) =>
        deriv.smulRight (tau⁻¹ • value)) hdp (congrFun hQ ((A.chart i.1).symm z.2))
    cases ch
    · exact congrArg₂ (fun f g : TangentSpace IM ((A.chart i.1).symm z.2) →L[ℝ] V => f-g) hdR hfastQ
    · exact congrArg₂ (fun f g : TangentSpace IM ((A.chart i.1).symm z.2) →L[ℝ] V => f+g) hdQ hfastR
  have hMean : physicalMean ((B i.2).symm z.1) ((A.chart i.1).symm z.2) =
      round4ParameterProbeArrayMean (I := IM) phases tau (nativeAmplitude false) (nativeAmplitude true)
        z.1 ((A.chart i.1).symm z.2) := by
    symm
    simp only [round4ParameterProbeArrayMean,hcoef]
    rfl
  apply actual_bilinear_tensor_eq_of_basis
  intro k l
  simp only [actualOriginalNativeTargetTensor_basis,actualPrimaryOppositeMeanTensor,
    actualRealTensorAssembly_basis]
  rw [hMean]
  exact (actualRepairModelFirstDefect_array_mean_observed_total (A.chart i.1) (hA.chart_mem i.1)
    phases tau (nativeAmplitude false) (nativeAmplitude true) z.1 z.2 hz.2 k l).symm

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_grouped_mean_native
