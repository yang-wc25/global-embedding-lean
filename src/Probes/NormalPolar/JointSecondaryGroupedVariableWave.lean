import NormalPolar.ParameterDisplacementVariableColumns
import NormalPolar.ParameterDisplacementPrescribedVariableJets
import NormalPolar.JointSecondaryGroupedWave

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
  {m N p r : ℕ} {Sub : Fin r → Type*} [∀ l, Fintype (Sub l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

theorem jointGroupedPrescribedWave_columns
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : (l : Fin r) → Sub l → Ep → D → M)
    (vf : (l : Fin r) → (s : Sub l) → (b : Ep) → (x : D) →
      normalSpace (I := I) (F b) (c l s b x))
    (phase : Fin r → Ep × M → ℝ) (tau : ℝ) (length : ℕ)
    (a : (l : Fin r) → Sub l → OpenPartialHomeomorph (Ep × M) X)
    (hA : ∀ l s, ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c l s z.1) z.2) (a l s).target)
    (hB : ∀ l s, ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c l s z.1) z.2) (a l s).target)
    (hBR : ∀ l s, ContDiffOn ℝ ∞ (fun z : X => fun i : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c l s z.1) z.2 0 i : V)) (a l s).target)
    (hvf : ∀ l s, ContDiffOn ℝ ∞ (fun z : X => (vf l s z.1 z.2 : V)) (a l s).target)
    (u : Fin p → ℝ) (z : Ep × M) :
    jointGroupedPrescribedWave label F hF c vf phase tau length a u z =
      ∑ q, u q • jointGroupedPrescribedWave label F hF c vf phase tau length a (Pi.single q 1) z := by
  have hscal (a b t : ℝ) (v w : V) :
      a • (t • v) - b • (t • w) = t • (a • v - b • w) := by
    rw [smul_sub,smul_comm a t,smul_comm b t]
  unfold jointGroupedPrescribedWave
  calc
    _ = ∑ l, ∑ q, u q • (Real.cos (phase l z/tau) •
        jointGroupedPrescribedAmplitude false label F hF c vf tau length a (Pi.single q 1) l z -
        Real.sin (phase l z/tau) •
        jointGroupedPrescribedAmplitude true label F hF c vf tau length a (Pi.single q 1) l z) := by
      apply Finset.sum_congr rfl
      intro l _
      rw [congrFun (jointGroupedPrescribedAmplitude_columns false label F hF c vf tau length a hA hB hBR hvf u l) z,
        congrFun (jointGroupedPrescribedAmplitude_columns true label F hF c vf tau length a hA hB hBR hvf u l) z]
      simp only [Finset.smul_sum,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro q _
      exact hscal _ _ _ _ _
    _ = _ := by rw [Finset.sum_comm]; simp only [Finset.smul_sum]

theorem jointGrouped_prescribed_variable_parameter_raw_jets
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : (l : Fin r) → Sub l → Ep → D → M) (chi : (l : Fin r) → Sub l → X → ℝ)
    (nu : (l : Fin r) → (s : Sub l) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l s b x))
    (a : (l : Fin r) → Sub l → OpenPartialHomeomorph (Ep × M) X) (W : Set (Ep × M)) (K : Fin r → Set (Ep × M))
    (pieceK : (l : Fin r) → Sub l → Set (Ep × M))
    (hW : IsOpen W) (hsub : ∀ l s, pieceK l s ⊆ K l) (n length j : ℕ) (horder : j+1+length ≤ n)
    (tau ell delta : ℝ) (weight : Fin r → ℝ) (Mg Bchi Bnu Ku : ℝ)
    (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hMg : 0 ≤ Mg) (hdelta : 0 ≤ delta) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu) (hKu : 0 ≤ Ku)
    (kappa : Y → Ep × M) (Omega S : Set Y) (hOmega : IsOpen Omega) (hS : S ⊆ Omega)
    (hkappa : ContinuousOn kappa Omega) (hmap : MapsTo kappa Omega W)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (phase : Fin r → Ep × M → ℝ) (Mphase : ℝ)
    (profiles : JointGroupedPrescribedObservationProfiles F hF c chi nu a W pieceK n j ell Mg Bchi Bnu
      kappa Omega S T phase Mphase)
    (L R : ℕ) (hL : ∀ y ∈ S, (Finset.univ.filter (fun l => kappa y ∈ K l)).card ≤ L)
    (hR : ∀ l y, y ∈ S → (Finset.univ.filter (fun s => kappa y ∈ pieceK l s)).card ≤ R)
    (u : Y → Fin p → ℝ) (hu : ContDiffOn ℝ ∞ u Omega)
    (hub : ∀ k ≤ j, ∀ y ∈ S, ell^k*‖iteratedFDeriv ℝ k u y‖ ≤ Ku) :
    let vf := fun l s => actualProbeNormalAmplitude F (c l s) (chi l s) (nu l s) delta tau (weight l)
    let wave := fun y => jointGroupedPrescribedWave label F hF c vf phase tau length a (u y) (kappa y)
    let C := actualVariablePrescribedWaveCost m N p n length j (L*R) T weight Mg Bchi Bnu Mphase Ku
    ContDiffOn ℝ ∞ wave Omega ∧
      ∀ k ≤ j, ∀ y ∈ S, tau^k*‖iteratedFDeriv ℝ k wave y‖ ≤ C*delta*tau := by
  intro vf wave C
  let column := fun q : Fin p => jointGroupedPrescribedWave label F hF c vf phase tau length a (Pi.single q 1) ∘ kappa
  let Ccolumn := actualFinitePrimaryJetConstant (L*R) N j Mphase
    (actualPrescribedRawAmplitudeCost m N n length j T weight Mg Bchi Bnu 1 false)
    (actualPrescribedRawAmplitudeCost m N n length j T weight Mg Bchi Bnu 1 true)
  have hCcolumn : 0 ≤ Ccolumn := actualFinitePrimaryJetConstant_nonneg (L*R) N j Mphase
    (actualPrescribedRawAmplitudeCost_nonneg m N n length j T weight Mg Bchi Bnu 1 false hT hMg hBchi hBnu zero_le_one)
    (actualPrescribedRawAmplitudeCost_nonneg m N n length j T weight Mg Bchi Bnu 1 true hT hMg hBchi hBnu zero_le_one)
  have hsingle (q : Fin p) : ‖(Pi.single q (1:ℝ) : Fin p → ℝ)‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).2
    intro k
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  have hraw (q : Fin p) := jointGrouped_prescribed_wave_from_raw label F hF c chi nu a W K pieceK hW hsub
    n length j horder tau ell delta weight Mg Bchi Bnu 1 htau htaul hell1 hMg hdelta hBchi hBnu zero_le_one
    kappa Omega S hOmega hS hkappa hmap T hT phase Mphase profiles L R hL hR (Pi.single q 1) (hsingle q)
  have hvf (l : Fin r) (s : Sub l) : ContDiffOn ℝ ∞ (fun z : X => (vf l s z.1 z.2 : V)) (a l s).target :=
    (((profiles.raw l s).cutoff_smooth.smul (profiles.raw l s).normal_smooth).const_smul
      (-(delta*tau)/(weight l)^2))
  have heq : wave = fun y => ∑ q, u y q • column q y := by
    funext y
    exact jointGroupedPrescribedWave_columns label F hF c vf phase tau length a
      (fun l s => (profiles.raw l s).A_smooth) (fun l s => (profiles.raw l s).B_smooth)
      (fun l s => (profiles.raw l s).BR_smooth) hvf (u y) (kappa y)
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

#print axioms GlobalEmbedding.Continuation.jointGroupedPrescribedWave_columns
#print axioms GlobalEmbedding.Continuation.jointGrouped_prescribed_variable_parameter_raw_jets
