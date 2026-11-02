import NormalPolar.JointSecondaryGroupedNativeMean
import NormalPolar.JointSecondaryGroupedMeanCost

/-! Primitive raw observation data for canonical parameter-chart pullbacks
of one global original-label grouped physical family. The fields being differentiated are determined
by the global F,c,cutoff,normal,phase and chart; no completed wave, mean or
derivative identity is a data field. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {M P : Type*} {m N d p r : ℕ}
  [TopologicalSpace P] [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  {Sub : Fin r → Type*} [∀ l, Fintype (Sub l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

structure JointGroupedPrescribedParameterChartRawData
    (F : P → M → V) (hF : ∀ b, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F b))
    (c : (l : Fin r) → Sub l → P → D → M) (chi : (l : Fin r) → Sub l → P × D → ℝ)
    (nu : (l : Fin r) → (s : Sub l) → (b : P) → (x : D) → normalSpace (I := 𝓙) (F b) (c l s b x))
    (phase : Fin r → P × M → ℝ)
    (a : (l : Fin r) → Sub l → OpenPartialHomeomorph (P × M) (P × D))
    (B : OpenPartialHomeomorph P Ep) (e : OpenPartialHomeomorph M D)
    (Omega S : Set X) (n j : ℕ) (ell Mg Bchi Bnu Mphase : ℝ) (T : ℕ → ℝ) where
  domain : Set (Ep × M)
  carrier : (l : Fin r) → Sub l → Set (Ep × M)
  domain_open : IsOpen domain
  observer_smooth : ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod 𝓙) ∞
    (fun z : X => (z.1,e.symm z.2)) Omega
  observer_domain : MapsTo (fun z : X => (z.1,e.symm z.2)) Omega domain
  raw : JointGroupedPrescribedObservationProfiles
    (fun b => F (B.symm b)) (fun b => hF (B.symm b))
    (fun l s b => c l s (B.symm b)) (fun l s z => chi l s (B.symm z.1,z.2))
    (fun l s b => nu l s (B.symm b)) (fun l s => round3ParameterChartPullback B (a l s))
    domain carrier n (j+1) ell Mg Bchi Bnu
    (fun z : X => (z.1,e.symm z.2)) Omega S T
    (fun l z => phase l (B.symm z.1,z.2)) Mphase

theorem jointGrouped_prescribed_parameter_chart_mean_from_raw
    (label : (Fin r × Bool) ↪ Fin p)
    (F : P → M → V) (hF : ∀ b, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F b))
    (c : (l : Fin r) → Sub l → P → D → M) (chi : (l : Fin r) → Sub l → P × D → ℝ)
    (nu : (l : Fin r) → (s : Sub l) → (b : P) → (x : D) → normalSpace (I := 𝓙) (F b) (c l s b x))
    (phase : Fin r → P × M → ℝ)
    (a : (l : Fin r) → Sub l → OpenPartialHomeomorph (P × M) (P × D))
    (ha : ∀ l s, Round3ParameterChartPreserves (a l s))
    (B : OpenPartialHomeomorph P Ep) (e : OpenPartialHomeomorph M D)
    (he : e ∈ maximalAtlas 𝓙 ∞ M) (Omega S : Set X)
    (hOmega : IsOpen Omega) (hS : S ⊆ Omega)
    (hTarget : Omega ⊆ B.target ×ˢ e.target)
    (n length j : ℕ) (horder : j+2+length ≤ n)
    (tau ell delta : ℝ) (weight : Fin r → ℝ) (Mg Bchi Bnu Mphase Ku : ℝ)
    (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hMg : 0 ≤ Mg) (hdelta : 0 ≤ delta) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu)
    (hMphase : 0 ≤ Mphase) (hKu : 0 ≤ Ku) (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (data : JointGroupedPrescribedParameterChartRawData F hF c chi nu phase a B e Omega S n j ell Mg Bchi Bnu Mphase T)
    (u : P → Fin p → ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : X => u (B.symm z.1)) Omega)
    (hub : ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k (fun z : X => u (B.symm z.1)) z‖ ≤ Ku)
    (i q : Fin (m+1)) :
    let vf := fun l s b x => (-(delta*tau)/(weight l)^2) • (chi l s (b,x) • nu l s b x)
    let w := fun z : X => fun k : Fin (m+1) => mfderiv 𝓘(ℝ,D) 𝓙 e.symm z.2
      ((tangentSpaceCastModel 𝓘(ℝ,D) z.2).symm (EuclideanSpace.single k 1))
    let mean := fun z => jointGroupedParameterPrescribedMean label F hF c vf phase tau length a
      (u (B.symm z.1)) (B.symm z.1) (e.symm z.2) (w z i) (w z q)
    let Kc := fun l => (Fintype.card (Sub l) : ℝ)*actualVariablePrescribedCoefficientCost m N p n length j T (weight l) Mg Bchi Bnu Mphase Ku
    let C := 2^j*‖incrementsMeanBilinear (Λ := Fin r) (N := N) i q‖*(∑ l, Kc l)^2
    ContDiffOn ℝ ∞ mean Omega ∧ ∀ k ≤ j, ∀ z ∈ S,
      ell^k*‖iteratedFDeriv ℝ k mean z‖ ≤ C*delta^2 := by
  intro vf w mean Kc C
  let Fn := fun b => F (B.symm b)
  let cn := fun l s b => c l s (B.symm b)
  let chin := fun (l : Fin r) (s : Sub l) (z : X) => chi l s (B.symm z.1,z.2)
  let nun := fun l s b => nu l s (B.symm b)
  let an := fun l s => round3ParameterChartPullback B (a l s)
  let phn := fun (l : Fin r) (z : Ep × M) => phase l (B.symm z.1,z.2)
  let vfn := fun l s => actualProbeNormalAmplitude Fn (cn l s) (chin l s) (nun l s) delta tau (weight l)
  let nativeMean := fun z : X => jointGroupedParameterPrescribedMean label Fn (fun b => hF (B.symm b))
    cn vfn phn tau length an (u (B.symm z.1)) z.1 (e.symm z.2) (w z i) (w z q)
  have heq : EqOn mean nativeMean Omega := by
    intro z hz
    have hh := jointGroupedParameterPrescribedMean_pullback label F hF c vf phase tau length a ha B
      (u (B.symm z.1)) z.1 (hTarget hz).1 (e.symm z.2)
    exact (congrArg (fun f => f (w z i) (w z q)) hh).symm
  have hraw := jointGrouped_prescribed_native_mean_from_raw label Fn (fun b => hF (B.symm b))
    cn chin nun an data.domain data.carrier data.domain_open n length j horder
    tau ell delta weight Mg Bchi Bnu Mphase Ku htau htaul hell1 hMg hdelta hBchi hBnu hMphase hKu
    (fun z : X => (z.1,e.symm z.2)) Omega S hOmega hS data.observer_smooth data.observer_domain T hT phn data.raw
    (fun z : X => u (B.symm z.1)) hu hub id e he rfl (fun z hz => (hTarget hz).2) i q
  refine ⟨hraw.1.congr heq,?_⟩
  intro k hk z hz
  rw [((heq.eventuallyEq_of_mem (hOmega.mem_nhds (hS hz))).iteratedFDeriv ℝ k).eq_of_nhds]
  exact hraw.2 k hk z hz

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointGrouped_prescribed_parameter_chart_mean_from_raw
