import NormalPolar.JointSecondaryGroupedDifference
import NormalPolar.JointSecondaryGroupedParameterRaw

/-! The two-parameter difference belongs to the same physical grouped mean
in every original native chart. Both pullbacks are identities of the actual
functions, so all original joint derivatives retain the quadratic factor. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open Set Filter Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {M Eq : Type*} {m N d p r : ℕ}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Eq] [NormedSpace ℝ Eq]
  {Sub : Fin r → Type*} [∀ l, Fintype (Sub l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "Y" => Eq × D
local notation "IM" => 𝓘(ℝ,D)

theorem jointGrouped_prescribed_native_mean_difference_from_raw
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (c : (l : Fin r) → Sub l → Ep → D → M) (chi : (l : Fin r) → Sub l → X → ℝ)
    (nu : (l : Fin r) → (s : Sub l) → (b : Ep) → (x : D) → normalSpace (I := IM) (F b) (c l s b x))
    (a : (l : Fin r) → Sub l → OpenPartialHomeomorph (Ep × M) X) (W : Set (Ep × M))
    (K : (l : Fin r) → Sub l → Set (Ep × M))
    (hW : IsOpen W) (n length j : ℕ) (horder : j+2+length ≤ n)
    (tau ell delta : ℝ) (weight : Fin r → ℝ) (Mg Bchi Bnu Mphase : ℝ)
    (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hMg : 0 ≤ Mg) (hdelta : 0 ≤ delta) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu)
    (hMphase : 0 ≤ Mphase)
    (kappa : Y → Ep × M) (Omega S : Set Y) (hOmega : IsOpen Omega) (hS : S ⊆ Omega)
    (hkappa : ContMDiffOn 𝓘(ℝ,Y) ((𝓘(ℝ,Ep)).prod IM) ∞ kappa Omega)
    (hmap : MapsTo kappa Omega W) (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (phase : Fin r → Ep × M → ℝ)
    (profiles : JointGroupedPrescribedObservationProfiles F hF c chi nu a W K n (j+1) ell Mg Bchi Bnu
      kappa Omega S T phase Mphase)
    (beta : Eq → Ep) (e : OpenPartialHomeomorph M D) (he : e ∈ maximalAtlas IM ∞ M)
    (hkappaEq : kappa = fun z => (beta z.1,e.symm z.2))
    (hOmegaSource : ∀ z ∈ Omega, z.2 ∈ e.target) (i q : Fin (m+1)) :
    let vf := fun l s => actualProbeNormalAmplitude F (c l s) (chi l s) (nu l s) delta tau (weight l)
    let w := fun z : Y => fun k : Fin (m+1) => mfderiv 𝓘(ℝ,D) IM e.symm z.2
      ((tangentSpaceCastModel 𝓘(ℝ,D) z.2).symm (EuclideanSpace.single k 1))
    let mean := fun u z => jointGroupedParameterPrescribedMean label F hF c vf phase tau length a u
      (beta z.1) (e.symm z.2) (w z i) (w z q)
    let Kc := fun l => (Fintype.card (Sub l) : ℝ)*actualVariablePrescribedCoefficientCost m N p n length j T (weight l) Mg Bchi Bnu Mphase 1
    let C := 2^j*‖incrementsMeanBilinear (Λ := Fin r) (N := N) i q‖*(∑ l, Kc l)^2
    ∀ u v : Fin p → ℝ, ContDiffOn ℝ ∞ (fun z => mean u z-mean v z) Omega ∧
      ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k (fun z => mean u z-mean v z) z‖ ≤
        C*delta^2*(‖u‖+‖v‖)*‖u-v‖ := by
  intro vf w mean Kc C
  let R := fun v => jointGroupedPrescribedAmplitude false label F hF c vf tau length a v
  let Q := fun v => jointGroupedPrescribedAmplitude true label F hF c vf tau length a v
  let amp := fun l ch v z => jointGroupedPrescribedAmplitude ch label F hF c vf tau length a v l (kappa z)
  let observed := fun u z => (incrementsOppositePrimaryContribution
    (fun l => actualDiagonalPhysicalCoefficient (phase l ∘ kappa) tau (amp l) u z) i q).re
  have heq (u : Fin p → ℝ) : EqOn (mean u) (observed u) Omega := by
    intro z hz
    have hh := (actualRepairModelFirstDefect_array_mean_observed_total e he phase tau
      (R u) (Q u) (beta z.1) z.2 (hOmegaSource z hz) i q).symm
    have hc : round4ParameterProbeArrayObservedCoefficient phase tau (R u) (Q u)
        (beta z.1) e.symm z.2 =
        fun l => actualDiagonalPhysicalCoefficient (phase l ∘ kappa) tau (amp l) u z := by
      funext l s co
      simp only [actualDiagonalPhysicalCoefficient,round4ParameterProbeArrayObservedCoefficient,
        Function.comp_apply,amp,R,Q,hkappaEq]
    rw [hc] at hh
    exact hh
  have hraw := jointGrouped_prescribed_mean_difference_from_raw label F hF c chi nu a W K hW
    n length j horder tau ell delta weight Mg Bchi Bnu Mphase htau htaul hell1
    hMg hdelta hBchi hBnu hMphase kappa Omega S hOmega hS hkappa hmap T hT phase profiles i q
  intro u v
  have he : EqOn (fun z => mean u z-mean v z) (fun z => observed u z-observed v z) Omega :=
    fun z hz => congrArg₂ (·-·) (heq u hz) (heq v hz)
  refine ⟨(hraw u v).1.congr he,?_⟩
  intro k hk z hz
  rw [((he.eventuallyEq_of_mem (hOmega.mem_nhds (hS hz))).iteratedFDeriv ℝ k).eq_of_nhds]
  exact (hraw u v).2 k hk z hz

variable {P : Type*} [TopologicalSpace P]

theorem jointGrouped_prescribed_parameter_chart_mean_difference_from_raw
    (label : (Fin r × Bool) ↪ Fin p)
    (F : P → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (c : (l : Fin r) → Sub l → P → D → M) (chi : (l : Fin r) → Sub l → P × D → ℝ)
    (nu : (l : Fin r) → (s : Sub l) → (b : P) → (x : D) → normalSpace (I := IM) (F b) (c l s b x))
    (phase : Fin r → P × M → ℝ)
    (a : (l : Fin r) → Sub l → OpenPartialHomeomorph (P × M) (P × D))
    (ha : ∀ l s, Round3ParameterChartPreserves (a l s))
    (B : OpenPartialHomeomorph P Ep) (e : OpenPartialHomeomorph M D)
    (he : e ∈ maximalAtlas IM ∞ M) (Omega S : Set X)
    (hOmega : IsOpen Omega) (hS : S ⊆ Omega) (hTarget : Omega ⊆ B.target ×ˢ e.target)
    (n length j : ℕ) (horder : j+2+length ≤ n)
    (tau ell delta : ℝ) (weight : Fin r → ℝ) (Mg Bchi Bnu Mphase : ℝ)
    (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hMg : 0 ≤ Mg) (hdelta : 0 ≤ delta) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu)
    (hMphase : 0 ≤ Mphase) (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (data : JointGroupedPrescribedParameterChartRawData F hF c chi nu phase a B e Omega S n j ell Mg Bchi Bnu Mphase T)
    (i q : Fin (m+1)) :
    let vf := fun l s b x => (-(delta*tau)/(weight l)^2) • (chi l s (b,x) • nu l s b x)
    let w := fun z : X => fun k : Fin (m+1) => mfderiv 𝓘(ℝ,D) IM e.symm z.2
      ((tangentSpaceCastModel 𝓘(ℝ,D) z.2).symm (EuclideanSpace.single k 1))
    let mean := fun u (z : X) => jointGroupedParameterPrescribedMean label F hF c vf phase tau length a
      u (B.symm z.1) (e.symm z.2) (w z i) (w z q)
    let Kc := fun l => (Fintype.card (Sub l) : ℝ)*actualVariablePrescribedCoefficientCost m N p n length j T (weight l) Mg Bchi Bnu Mphase 1
    let C := 2^j*‖incrementsMeanBilinear (Λ := Fin r) (N := N) i q‖*(∑ l, Kc l)^2
    ∀ u v : Fin p → ℝ, ContDiffOn ℝ ∞ (fun z => mean u z-mean v z) Omega ∧
      ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k (fun z => mean u z-mean v z) z‖ ≤
        C*delta^2*(‖u‖+‖v‖)*‖u-v‖ := by
  intro vf w mean Kc C
  let Fn := fun b => F (B.symm b)
  let cn := fun l s b => c l s (B.symm b)
  let chin := fun (l : Fin r) (s : Sub l) (z : X) => chi l s (B.symm z.1,z.2)
  let nun := fun l s b => nu l s (B.symm b)
  let an := fun l s => round3ParameterChartPullback B (a l s)
  let phn := fun (l : Fin r) (z : Ep × M) => phase l (B.symm z.1,z.2)
  let vfn := fun l s => actualProbeNormalAmplitude Fn (cn l s) (chin l s) (nun l s) delta tau (weight l)
  let nativeMean := fun u (z : X) => jointGroupedParameterPrescribedMean label Fn (fun b => hF (B.symm b))
    cn vfn phn tau length an u z.1 (e.symm z.2) (w z i) (w z q)
  have heq (u : Fin p → ℝ) : EqOn (mean u) (nativeMean u) Omega := by
    intro z hz
    have hh := jointGroupedParameterPrescribedMean_pullback label F hF c vf phase tau length a ha B
      u z.1 (hTarget hz).1 (e.symm z.2)
    exact (congrArg (fun f => f (w z i) (w z q)) hh).symm
  have hraw := jointGrouped_prescribed_native_mean_difference_from_raw label Fn (fun b => hF (B.symm b))
    cn chin nun an data.domain data.carrier data.domain_open n length j horder
    tau ell delta weight Mg Bchi Bnu Mphase htau htaul hell1 hMg hdelta hBchi hBnu hMphase
    (fun z : X => (z.1,e.symm z.2)) Omega S hOmega hS data.observer_smooth data.observer_domain T hT phn data.raw
    id e he rfl (fun z hz => (hTarget hz).2) i q
  intro u v
  have he : EqOn (fun z => mean u z-mean v z) (fun z => nativeMean u z-nativeMean v z) Omega :=
    fun z hz => congrArg₂ (·-·) (heq u hz) (heq v hz)
  refine ⟨(hraw u v).1.congr he,?_⟩
  intro k hk z hz
  rw [((he.eventuallyEq_of_mem (hOmega.mem_nhds (hS hz))).iteratedFDeriv ℝ k).eq_of_nhds]
  exact (hraw u v).2 k hk z hz

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointGrouped_prescribed_native_mean_difference_from_raw
#print axioms GlobalEmbedding.Continuation.jointGrouped_prescribed_parameter_chart_mean_difference_from_raw
