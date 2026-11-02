import NormalPolar.JointSecondaryAmplitude
import NormalPolar.ActualRepairModelFirstDefectCoefficient
import NormalPolar.ParameterDisplacementPrescribedWave

/-! The common background-plus-prescribed array supplies its own coefficient
regularity, opposite-mean regularity and grouped derivative. Every amplitude is
the same finite reconstruction and every inactive mode uses its actual zero
germ. The background phase is used only on its primitive primary neighborhood.
The parameter is inserted into the original amplitudes before differentiating.
No whole-wave, coefficient or mean regularity is an input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {E H M Ep Eq : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Eq] [NormedSpace ℝ Eq]
  {m N p r : ℕ} {Λ Β : Type*} [Fintype Λ] [DecidableEq Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Y" => Eq × D

theorem jointSecondary_common_regular_from_primitives
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (label : (Fin r × Bool) ↪ Fin p)
    (c : Fin r → Ep → D → M) (chi : Fin r → X → ℝ)
    (nu : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (input : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (W : Set (Ep × M)) (K : (Λ ⊕ Fin r) → Set (Ep × M))
    (background : ParameterRound2GlobalMeanPrimitives F hF g input W (fun l => K (Sum.inl l)))
    (n j backgroundLength probeLength : ℕ) (ell Mg Bchi Bnu tau delta : ℝ) (weight : Fin r → ℝ)
    (kappa : Y → Ep × M) (Omega S : Set Y) (hOmega : IsOpen Omega)
    (hkappa : ContMDiffOn 𝓘(ℝ,Y) ((𝓘(ℝ,Ep)).prod I) ∞ kappa Omega)
    (hmap : MapsTo kappa Omega W) (T : ℕ → ℝ) (Mphase : ℝ)
    (prescribed : ActualPrescribedObservationProfiles F hF c chi nu a W (fun l => K (Sum.inr l))
      n j ell Mg Bchi Bnu kappa Omega S T phase Mphase)
    (u : Ep → Fin p → ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : Y => u (kappa z).1) Omega) :
    let vf := fun l => actualProbeNormalAmplitude F (c l) (chi l) (nu l) delta tau (weight l)
    let phases := Sum.elim g.phase phase
    let R := jointSecondaryCombinedAmplitude F hF g label c vf tau delta backgroundLength probeLength a input u false
    let Q := jointSecondaryCombinedAmplitude F hF g label c vf tau delta backgroundLength probeLength a input u true
    let coeff := incrementsSecondaryPhysicalCoefficient (fun l b x => phases l (kappa (b,x))) tau
      (fun (_ : Λ ⊕ Fin r) (_ : Eq) (_ : Unit) _ => 1)
      (fun l b (_ : Unit) x => R l (kappa (b,x))) (fun l b (_ : Unit) x => Q l (kappa (b,x)))
      (fun i _ => EuclideanSpace.single i 1)
    (∀ l, ContDiffOn ℝ ∞ (fun z => coeff z l) Omega) ∧
    ContDiffOn ℝ ∞ (actualPrimaryOppositeMeanTensor (fun l b x => phases l (kappa (b,x))) tau
      (fun (_ : Λ ⊕ Fin r) (_ : Eq) (_ : Unit) _ => 1)
      (fun l b (_ : Unit) x => R l (kappa (b,x))) (fun l b (_ : Unit) x => Q l (kappa (b,x)))) Omega ∧
    ∀ z ∈ Omega, ∀ i,
      fderiv ℝ (fun x => round4ParameterProbeCombinedPrimary F hF g label c vf phase tau delta
        backgroundLength probeLength a input (u (kappa (z.1,x)).1) (kappa (z.1,x))) z.2 (EuclideanSpace.single i 1) =
        incrementsGroupedRealDerivative (fun l => phases l (kappa z)/tau) (coeff z) i := by
  intro vf phases R Q coeff
  have hsupp := jointSecondary_common_amplitude_support F hF g label c chi nu a input W K
    background n j backgroundLength probeLength ell Mg Bchi Bnu tau delta weight prescribed.raw u
  have hfixed (v : Fin p → ℝ) := actualRepairModelFirstDefect_common_amplitude_regular
    F hF g label c chi nu a input W K background n j backgroundLength probeLength
    ell Mg Bchi Bnu tau delta weight prescribed.raw v
  have hamp (ch : Bool) (l : Λ ⊕ Fin r) :
      ContDiffOn ℝ ∞ (jointSecondaryCombinedAmplitude F hF g label c vf tau delta
        backgroundLength probeLength a input u ch l ∘ kappa) Omega := by
    cases l with
    | inl l => exact (((hfixed 0 ch (Sum.inl l)).1).comp hkappa hmap).contDiffOn
    | inr l =>
      have hvf : ContDiffOn ℝ ∞ (fun z : X => (vf l z.1 z.2 : V)) (a l).target :=
        (((prescribed.raw l).cutoff_smooth.smul (prescribed.raw l).normal_smooth).const_smul
          (-(delta*tau)/(weight l)^2))
      have heq :
          (jointSecondaryCombinedAmplitude F hF g label c vf tau delta
            backgroundLength probeLength a input u ch (Sum.inr l) ∘ kappa) =
          (fun z => ∑ q : Fin p, u (kappa z).1 q •
            round4PrescribedGlobalAmplitude ch label l F hF (c l) (vf l) tau probeLength
              (a l) (Pi.single q 1) (kappa z)) := by
        funext z
        exact congrFun (round4PrescribedGlobalAmplitude_columns ch label l F hF (c l) (vf l)
          tau probeLength (a l) (prescribed.raw l).A_smooth (prescribed.raw l).B_smooth
          (prescribed.raw l).BR_smooth hvf (u (kappa z).1)) (kappa z)
      rw [heq]
      apply ContDiffOn.sum
      intro q _
      exact ((ContinuousLinearMap.proj q).contDiff.comp_contDiffOn hu).smul
        ((((hfixed (Pi.single q 1) ch (Sum.inr l)).1).comp hkappa hmap).contDiffOn)
  have hR : ∀ l, ContDiffOn ℝ ∞ (R l ∘ kappa) Omega := hamp false
  have hQ : ∀ l, ContDiffOn ℝ ∞ (Q l ∘ kappa) Omega := hamp true
  let O : (Λ ⊕ Fin r) → Set Y := Sum.elim
    (fun l => Omega ∩ kappa ⁻¹' K (Sum.inl l)) prescribed.domains
  have hO : ∀ l, IsOpen (O l) := by
    intro l
    cases l with
    | inl l => exact hkappa.continuousOn.isOpen_inter_preimage hOmega (background.hPrimary l)
    | inr l => exact prescribed.domains_open l
  have hcover : ∀ l, Omega ∩ kappa ⁻¹' K l ⊆ O l := by
    intro l
    cases l with
    | inl l => exact subset_rfl
    | inr l => exact prescribed.active_domain l
  have hp : ∀ l, ContDiffOn ℝ ∞ (phases l ∘ kappa) (O l) := by
    intro l
    cases l with
    | inl l =>
      exact ((background.hPhase l).comp (hkappa.mono inter_subset_left)
        (fun z hz => ⟨hmap hz.1,hz.2⟩)).contDiffOn
    | inr l => exact prescribed.phase_smooth l
  refine ⟨?_,?_,?_⟩
  · exact actualRepairModelFirstDefect_supported_coefficient_contDiffOn phases tau R Q W background.hW K
      (hsupp false) (hsupp true) kappa Omega hOmega hkappa.continuousOn hmap
      O hO hcover hp hR hQ
  · exact actualRepairModelFirstDefect_supported_mean_contDiffOn phases tau R Q W background.hW K
      (hsupp false) (hsupp true) kappa Omega hOmega hkappa.continuousOn hmap
      O hO hcover hp hR hQ
  · intro z hz i
    exact actual_supported_primary_observed_grouped_derivative phases tau R Q W background.hW K
      (hsupp false) (hsupp true) kappa Omega hOmega hkappa.continuousOn hmap
      O hO hcover hp hR hQ z hz i

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondary_common_regular_from_primitives
