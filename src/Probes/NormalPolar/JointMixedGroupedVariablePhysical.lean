import NormalPolar.JointMixedVariablePhysical
import NormalPolar.JointMixedGroupedPhysical
import NormalPolar.JointSecondaryGroupedVariableWave

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m N p r : ℕ} {Sub : Fin r → Type*} [∀ l, Fintype (Sub l)] {Ep Eq M : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Eq] [NormedSpace ℝ Eq]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Y" => Eq × D
local notation "IM" => 𝓘(ℝ,D)
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ

private local instance jointVariablePhysicalTensorSemi : SeminormedAddCommGroup Tensor :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance jointVariablePhysicalTensorNormed : NormedAddCommGroup Tensor :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance jointVariablePhysicalTensorSpace : NormedSpace ℝ Tensor :=
  ContinuousLinearMap.toNormedSpace

theorem jointGrouped_prescribed_variable_physical_from_raw
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (c : (l : Fin r) → Sub l → Ep → D → M) (chi : (l : Fin r) → Sub l → X → ℝ)
    (nu : (l : Fin r) → (s : Sub l) → (b : Ep) → (x : D) → normalSpace (I := IM) (F b) (c l s b x))
    (a : (l : Fin r) → Sub l → OpenPartialHomeomorph (Ep × M) X) (W : Set (Ep × M)) (K : Fin r → Set (Ep × M))
    (pieceK : (l : Fin r) → Sub l → Set (Ep × M))
    (hW : IsOpen W) (hsub : ∀ l s, pieceK l s ⊆ K l) (n length j : ℕ) (horder : j+length ≤ n)
    (tau ell delta : ℝ) (weight : Fin r → ℝ) (Mg Bchi Bnu Ku : ℝ)
    (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hdelta : 0 ≤ delta) (hweight : ∀ l, weight l ≠ 0)
    (hMg : 0 ≤ Mg) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu) (hKu : 0 ≤ Ku)
    (kappa : Y → Ep × M) (parameter : Eq → Ep) (hfirst : ∀ z, (kappa z).1 = parameter z.1)
    (Omega S : Set Y) (hOmega : IsOpen Omega) (hS : S ⊆ Omega)
    (hkappa : ContinuousOn kappa Omega) (hmap : MapsTo kappa Omega W)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (phase : Fin r → Ep × M → ℝ) (Mphase : ℝ)
    (profiles : JointGroupedPrescribedObservationProfiles F hF c chi nu a W pieceK n (j+1) ell Mg Bchi Bnu
      kappa Omega S T phase Mphase)
    (geom : ∀ l s, ActualPrescribedPhysicalGeometry F hF (c l s) (nu l s) (a l s) (phase l))
    (L R : ℕ) (hL : ∀ y ∈ S, (Finset.univ.filter (fun l => kappa y ∈ K l)).card ≤ L)
    (hR : ∀ l y, y ∈ S → (Finset.univ.filter (fun s => kappa y ∈ pieceK l s)).card ≤ R)
    (u : Eq → Fin p → ℝ) (hu : ContDiffOn ℝ ∞ (fun y : Y => u y.1) Omega)
    (hub : ∀ k ≤ j, ∀ y ∈ S, ell^k*‖iteratedFDeriv ℝ k (fun z : Y => u z.1) y‖ ≤ Ku) :
    let vf := fun l s => actualProbeNormalAmplitude F (c l s) (chi l s) (nu l s) delta tau (weight l)
    let Fobs := fun z : Y => F (kappa z).1 (kappa z).2
    let wave := fun y : Y => jointGroupedPrescribedWave label F hF c vf phase tau length a (u y.1) (kappa y)
    let E := actualJointMetricLinearization Fobs wave
    let C := jointMixedVariablePrescribedPhysicalCost m N p n length j (L*R) T weight Mg Bchi Bnu Ku
    ContDiffOn ℝ ∞ wave Omega ∧ ContDiffOn ℝ ∞ E Omega ∧
      ∀ k ≤ j, ∀ y ∈ S, tau^k*‖iteratedFDeriv ℝ k E y‖ ≤ C*delta*tau*(tau/ell)^length := by
  intro vf Fobs wave E C
  let column := fun q : Fin p => jointGroupedPrescribedWave label F hF c vf phase tau length a
    (Pi.single q 1) ∘ kappa
  let Ecolumn := fun q => actualJointMetricLinearization Fobs (column q)
  let Ccolumn := ((L*R : ℕ) : ℝ)*actualPrescribedRawPhysicalCost m N n length j T weight Mg Bchi Bnu
  have hCcolumn : 0 ≤ Ccolumn := mul_nonneg (Nat.cast_nonneg _) (actualPrescribedRawPhysicalCost_nonneg
    m N n length j T weight Mg Bchi Bnu hT hMg hBchi hBnu)
  have hell : 0 < ell := htau.trans_le htaul
  have hsingle (q : Fin p) : ‖(Pi.single q (1:ℝ) : Fin p → ℝ)‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).2
    intro k
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  have hraw (q : Fin p) := jointGrouped_prescribed_global_physical_from_raw label F hF c chi nu a W K pieceK hW hsub
    n length j horder tau ell delta weight Mg Bchi Bnu 1 htau htaul hell1 hdelta hweight
    hMg hBchi hBnu zero_le_one kappa parameter hfirst Omega S hOmega hS hkappa hmap T hT phase Mphase
    profiles geom L R hL hR (Pi.single q 1) (hsingle q)
  have hvf (l : Fin r) (s : Sub l) : ContDiffOn ℝ ∞ (fun z : X => (vf l s z.1 z.2 : V)) (a l s).target :=
    (((profiles.raw l s).cutoff_smooth.smul (profiles.raw l s).normal_smooth).const_smul
      (-(delta*tau)/(weight l)^2))
  have hcolumns (v : Fin p → ℝ) (y : Y) :
      jointGroupedPrescribedWave label F hF c vf phase tau length a v (kappa y) =
        ∑ q, v q • column q y :=
    jointGroupedPrescribedWave_columns label F hF c vf phase tau length a
      (fun l s => (profiles.raw l s).A_smooth) (fun l s => (profiles.raw l s).B_smooth)
      (fun l s => (profiles.raw l s).BR_smooth) hvf v (kappa y)
  have hwave : wave = fun y => ∑ q, u y.1 q • column q y := funext (fun y => hcolumns (u y.1) y)
  have heq : EqOn E (fun y => ∑ q, u y.1 q • Ecolumn q y) Omega := by
    intro y hy
    exact jointMixed_variable_linearization_columns Fobs column
      (fun v y => jointGroupedPrescribedWave label F hF c vf phase tau length a v (kappa y))
      Omega hOmega (fun q => (hraw q).1) (fun v y _ => hcolumns v y) u y hy
  have hjets := actual_variable_columns_weighted_jets j (fun y : Y => u y.1) Ecolumn
    Omega S hOmega hS hu (fun q => (hraw q).2.1)
    tau ell Ku (Ccolumn*delta*tau*(tau/ell)^length) htau htaul hKu (by positivity) hub
    (fun q k hk y hy => by simpa only [mul_one] using (hraw q).2.2 k hk y hy)
  refine ⟨?_,hjets.1.congr heq,?_⟩
  · rw [hwave]
    apply ContDiffOn.sum
    intro q _
    exact ((ContinuousLinearMap.proj q).contDiff.comp_contDiffOn hu).smul (hraw q).1
  · intro k hk y hy
    have he : E =ᶠ[𝓝 y] (fun z => ∑ q, u z.1 q • Ecolumn q z) :=
      eventuallyEq_of_mem (hOmega.mem_nhds (hS hy)) (fun z hz => heq hz)
    rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
    exact (hjets.2 k hk y hy).trans_eq (by dsimp only [C,jointMixedVariablePrescribedPhysicalCost,Ccolumn]; ring)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.jointGrouped_prescribed_variable_physical_from_raw
