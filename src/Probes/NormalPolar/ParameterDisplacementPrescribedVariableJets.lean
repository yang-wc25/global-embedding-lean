import NormalPolar.ParameterDisplacementVariableColumns
import NormalPolar.ParameterDisplacementPrescribedWave

/-!
# Full joint jets of the actual prescribed wave at a variable parameter

The parameter is an actual smooth function of the observation variables.
The exact full-wave column identity retains both reconstruction channels;
the slow derivatives of the parameter are included in every product jet.
The constant is fixed by the original primitive profiles before the scales,
fields and parameter function are chosen.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {E H M Ep Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {m N p r : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

def actualVariablePrescribedWaveCost (m N p n length j L : ℕ)
    (T : ℕ → ℝ) (weight : Fin r → ℝ) (Mg Bchi Bnu Mphase Ku : ℝ) : ℝ :=
  ((p : ℝ)*2^j*Ku)*actualFinitePrimaryJetConstant L N j Mphase
    (actualPrescribedRawAmplitudeCost m N n length j T weight Mg Bchi Bnu 1 false)
    (actualPrescribedRawAmplitudeCost m N n length j T weight Mg Bchi Bnu 1 true)

theorem actualVariablePrescribedWaveCost_nonneg (m N p n length j L : ℕ)
    (T : ℕ → ℝ) (weight : Fin r → ℝ) (Mg Bchi Bnu Mphase Ku : ℝ)
    (hT : ∀ k, 0 ≤ T k) (hMg : 0 ≤ Mg) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu) (hKu : 0 ≤ Ku) :
    0 ≤ actualVariablePrescribedWaveCost m N p n length j L T weight Mg Bchi Bnu Mphase Ku := by
  exact mul_nonneg (by positivity) (actualFinitePrimaryJetConstant_nonneg L N j Mphase
    (actualPrescribedRawAmplitudeCost_nonneg m N n length j T weight Mg Bchi Bnu 1 false hT hMg hBchi hBnu zero_le_one)
    (actualPrescribedRawAmplitudeCost_nonneg m N n length j T weight Mg Bchi Bnu 1 true hT hMg hBchi hBnu zero_le_one))

theorem actual_prescribed_variable_parameter_raw_jets
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M) (chi : Fin r → X → ℝ)
    (nu : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X) (W : Set (Ep × M)) (K : Fin r → Set (Ep × M))
    (hW : IsOpen W) (n length j : ℕ) (horder : j+1+length ≤ n)
    (tau ell delta : ℝ) (weight : Fin r → ℝ) (Mg Bchi Bnu Ku : ℝ)
    (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hMg : 0 ≤ Mg) (hdelta : 0 ≤ delta) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu) (hKu : 0 ≤ Ku)
    (kappa : Y → Ep × M) (Omega S : Set Y) (hOmega : IsOpen Omega) (hS : S ⊆ Omega)
    (hkappa : ContinuousOn kappa Omega) (hmap : MapsTo kappa Omega W)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (phase : Fin r → Ep × M → ℝ) (Mphase : ℝ)
    (profiles : ActualPrescribedObservationProfiles F hF c chi nu a W K n j ell Mg Bchi Bnu
      kappa Omega S T phase Mphase)
    (L : ℕ) (hL : ∀ y ∈ S, (Finset.univ.filter (fun l => kappa y ∈ K l)).card ≤ L)
    (u : Y → Fin p → ℝ) (hu : ContDiffOn ℝ ∞ u Omega)
    (hub : ∀ k ≤ j, ∀ y ∈ S, ell^k*‖iteratedFDeriv ℝ k u y‖ ≤ Ku) :
    let vf := fun l => actualProbeNormalAmplitude F (c l) (chi l) (nu l) delta tau (weight l)
    let wave := fun y => round4PrescribedGlobalWave label F hF c vf phase tau length a (u y) (kappa y)
    let C := actualVariablePrescribedWaveCost m N p n length j L T weight Mg Bchi Bnu Mphase Ku
    ContDiffOn ℝ ∞ wave Omega ∧
      ∀ k ≤ j, ∀ y ∈ S, tau^k*‖iteratedFDeriv ℝ k wave y‖ ≤ C*delta*tau := by
  intro vf wave C
  let column := fun q : Fin p => round4PrescribedGlobalWave label F hF c vf phase tau length a (Pi.single q 1) ∘ kappa
  let Ccolumn := actualFinitePrimaryJetConstant L N j Mphase
    (actualPrescribedRawAmplitudeCost m N n length j T weight Mg Bchi Bnu 1 false)
    (actualPrescribedRawAmplitudeCost m N n length j T weight Mg Bchi Bnu 1 true)
  have hCcolumn : 0 ≤ Ccolumn := actualFinitePrimaryJetConstant_nonneg L N j Mphase
    (actualPrescribedRawAmplitudeCost_nonneg m N n length j T weight Mg Bchi Bnu 1 false hT hMg hBchi hBnu zero_le_one)
    (actualPrescribedRawAmplitudeCost_nonneg m N n length j T weight Mg Bchi Bnu 1 true hT hMg hBchi hBnu zero_le_one)
  have hsingle (q : Fin p) : ‖(Pi.single q (1:ℝ) : Fin p → ℝ)‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).2
    intro k
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  have hraw (q : Fin p) := actual_prescribed_wave_from_raw label F hF c chi nu a W K hW
    n length j horder tau ell delta weight Mg Bchi Bnu 1 htau htaul hell1 hMg hdelta hBchi hBnu zero_le_one
    kappa Omega S hOmega hS hkappa hmap T hT phase Mphase profiles L hL (Pi.single q 1) (hsingle q)
  have hvf (l : Fin r) : ContDiffOn ℝ ∞ (fun z : X => (vf l z.1 z.2 : V)) (a l).target :=
    (((profiles.raw l).cutoff_smooth.smul (profiles.raw l).normal_smooth).const_smul
      (-(delta*tau)/(weight l)^2))
  have heq : wave = fun y => ∑ q, u y q • column q y := by
    funext y
    exact round4PrescribedGlobalWave_columns label F hF c vf phase tau length a
      (fun l => (profiles.raw l).A_smooth) (fun l => (profiles.raw l).B_smooth)
      (fun l => (profiles.raw l).BR_smooth) hvf (u y) (kappa y)
  have hh := actual_variable_columns_weighted_jets j u column Omega S hOmega hS hu
    (fun q => (hraw q).1) tau ell Ku (Ccolumn*delta*tau) htau htaul hKu (by positivity) hub
    (fun q => (hraw q).2)
  refine ⟨?_,?_⟩
  · rw [heq]
    exact hh.1
  · intro k hk y hy
    rw [heq]
    exact (hh.2 k hk y hy).trans_eq (by dsimp only [C,actualVariablePrescribedWaveCost,Ccolumn]; ring)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_prescribed_variable_parameter_raw_jets
