import NormalPolar.JointSecondaryGroupedMean
import NormalPolar.JointSecondaryGroupedParameter
import NormalPolar.ActualRepairModelFirstDefectTotalCoordinates

/-! The actual native grouped prescribed tensor, observed through a genuine inverse
source chart and the original parameter map, receives the variable-parameter
slow joint mean budget. Total derivatives preserve the identity even for
inactive nonsmooth phases; no global phase regularity is added. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
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
local notation "𝓙" => 𝓘(ℝ,D)

theorem jointGrouped_prescribed_native_mean_from_raw
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F b))
    (c : (l : Fin r) → Sub l → Ep → D → M) (chi : (l : Fin r) → Sub l → X → ℝ)
    (nu : (l : Fin r) → (s : Sub l) → (b : Ep) → (x : D) → normalSpace (I := 𝓙) (F b) (c l s b x))
    (a : (l : Fin r) → Sub l → OpenPartialHomeomorph (Ep × M) X) (W : Set (Ep × M))
    (K : (l : Fin r) → Sub l → Set (Ep × M))
    (hW : IsOpen W) (n length j : ℕ) (horder : j+2+length ≤ n)
    (tau ell delta : ℝ) (weight : Fin r → ℝ) (Mg Bchi Bnu Mphase Ku : ℝ)
    (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hMg : 0 ≤ Mg) (hdelta : 0 ≤ delta) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu)
    (hMphase : 0 ≤ Mphase) (hKu : 0 ≤ Ku)
    (kappa : Y → Ep × M) (Omega S : Set Y) (hOmega : IsOpen Omega) (hS : S ⊆ Omega)
    (hkappa : ContMDiffOn 𝓘(ℝ,Y) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ kappa Omega)
    (hmap : MapsTo kappa Omega W) (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (phase : Fin r → Ep × M → ℝ)
    (profiles : JointGroupedPrescribedObservationProfiles F hF c chi nu a W K n (j+1) ell Mg Bchi Bnu
      kappa Omega S T phase Mphase)
    (u : Y → Fin p → ℝ) (hu : ContDiffOn ℝ ∞ u Omega)
    (hub : ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k u z‖ ≤ Ku) (beta : Eq → Ep) (e : OpenPartialHomeomorph M D)
    (he : e ∈ maximalAtlas 𝓙 ∞ M)
    (hkappaEq : kappa = fun z => (beta z.1,e.symm z.2))
    (hOmegaSource : ∀ z ∈ Omega, z.2 ∈ e.target) (i q : Fin (m+1)) :
    let vf := fun l s => actualProbeNormalAmplitude F (c l s) (chi l s) (nu l s) delta tau (weight l)
    let w := fun z : Y => fun k : Fin (m+1) => mfderiv 𝓘(ℝ,D) 𝓙 e.symm z.2
      ((tangentSpaceCastModel 𝓘(ℝ,D) z.2).symm (EuclideanSpace.single k 1))
    let mean := fun z => jointGroupedParameterPrescribedMean label F hF c vf phase tau length a (u z)
      (beta z.1) (e.symm z.2) (w z i) (w z q)
    let Kc := fun l => (Fintype.card (Sub l) : ℝ)*actualVariablePrescribedCoefficientCost m N p n length j T (weight l) Mg Bchi Bnu Mphase Ku
    let C := 2^j*‖incrementsMeanBilinear (Λ := Fin r) (N := N) i q‖*(∑ l, Kc l)^2
    ContDiffOn ℝ ∞ mean Omega ∧ ∀ k ≤ j, ∀ z ∈ S,
      ell^k*‖iteratedFDeriv ℝ k mean z‖ ≤ C*delta^2 := by
  intro vf w mean Kc C
  let R := fun v => jointGroupedPrescribedAmplitude false label F hF c vf tau length a v
  let Q := fun v => jointGroupedPrescribedAmplitude true label F hF c vf tau length a v
  let amp := fun l ch v z => jointGroupedPrescribedAmplitude ch label F hF c vf tau length a v l (kappa z)
  let observed := fun z => (incrementsOppositePrimaryContribution
    (fun l => actualDiagonalPhysicalCoefficient (phase l ∘ kappa) tau (amp l) (u z) z) i q).re
  have heq : EqOn mean observed Omega := by
    intro z hz
    have hh := (actualRepairModelFirstDefect_array_mean_observed_total e he phase tau
      (R (u z)) (Q (u z)) (beta z.1) z.2 (hOmegaSource z hz) i q).symm
    have hcoeff : round4ParameterProbeArrayObservedCoefficient phase tau (R (u z)) (Q (u z))
        (beta z.1) e.symm z.2 =
        fun l => actualDiagonalPhysicalCoefficient (phase l ∘ kappa) tau (amp l) (u z) z := by
      funext l s co
      simp only [actualDiagonalPhysicalCoefficient,round4ParameterProbeArrayObservedCoefficient,
        Function.comp_apply,amp,R,Q,hkappaEq]
    rw [hcoeff] at hh
    exact hh
  have hraw := jointGrouped_prescribed_mean_from_raw label F hF c chi nu a W K hW
    n length j horder tau ell delta weight Mg Bchi Bnu Mphase Ku htau htaul hell1
    hMg hdelta hBchi hBnu hMphase hKu kappa Omega S hOmega hS hkappa hmap T hT phase profiles u hu hub i q
  refine ⟨hraw.1.congr heq,?_⟩
  intro k hk z hz
  rw [((heq.eventuallyEq_of_mem (hOmega.mem_nhds (hS hz))).iteratedFDeriv ℝ k).eq_of_nhds]
  exact hraw.2 k hk z hz

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointGrouped_prescribed_native_mean_from_raw
