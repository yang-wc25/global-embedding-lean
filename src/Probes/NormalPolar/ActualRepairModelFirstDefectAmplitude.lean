import NormalPolar.ParameterDisplacementPrescribedRaw
import Smoothing.ParameterRound2MeanPrimitives
import Probes.Round4ParameterProbeCombinedPrimary

/-! The literal common-array amplitudes are smooth and supported by their
original carriers, directly from the background primitive packet and the
prescribed raw normal source. Both reconstruction channels and every
subordinate background term are retained. No amplitude output hypothesis is
introduced. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff BigOperators Classical
namespace GlobalEmbedding.Continuation

theorem actualRepairModelFirstDefect_finite_sum_support
    {X V Index : Type*} [TopologicalSpace X] [AddCommMonoid V] [Fintype Index]
    (f : Index → X → V) (K : Set X) (h : ∀ i, tsupport (f i) ⊆ K) :
    tsupport (fun x => ∑ i, f i x) ⊆ K := by
  have hs (s : Finset Index) : tsupport (fun x => ∑ i ∈ s, f i x) ⊆ K := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (tsupport_add (f a) (fun x => ∑ i ∈ s, f i x)).trans (union_subset (h a) ih)
  exact hs Finset.univ

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N p r : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

theorem actualRepairModelFirstDefect_background_amplitude_regular
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (W : Set (Ep × M)) (K : Λ → Set (Ep × M))
    (raw : ParameterRound2GlobalMeanPrimitives F hF g input W K)
    (length : ℕ) (tau : ℝ) :
    ∀ ch l, ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,V) ∞
      (incrementsGlobalPrimaryAmplitude F hF g input length tau ch l) W ∧
      tsupport (fun z : W => incrementsGlobalPrimaryAmplitude F hF g input length tau ch l z) ⊆
        Subtype.val ⁻¹' K l := by
  have hr := actual_global_primary_extension_regular F hF g input length tau W raw.hW K raw.hPrimary
    raw.hPrimarySupport raw.hSourceW raw.hChart raw.hChartInv raw.hInverse raw.hCombinedSupport
    raw.hCut raw.hNormal raw.hArgument raw.hEta raw.hPositive raw.hG raw.hJ raw.hT0 raw.hA raw.hB raw.hSecond
  intro ch l
  have hext (q : Β) : ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,V) ∞
      (incrementsGlobalPrimaryExtension F hF g input length tau ch l q) W := by
    cases ch with
    | false => exact (hr l q).2.2.2.1
    | true => exact (hr l q).2.2.1
  have hs (q : Β) : tsupport (fun z : W => incrementsGlobalPrimaryExtension F hF g input length tau ch l q z) ⊆
      Subtype.val ⁻¹' K l := by
    have hcut : incrementsGlobalRelativeSupport W (fun z => g.eta l q z*g.cutoff l z) ⊆
        incrementsGlobalRelativeSupport W (g.cutoff l) := by
      rw [parameterRound2_global_relativeSupport_eq W raw.hW,parameterRound2_global_relativeSupport_eq W raw.hW]
      exact inter_subset_inter_right W tsupport_mul_subset_right
    have hbase : tsupport (fun z : W => incrementsGlobalPrimaryExtension F hF g input length tau ch l q z) ⊆
        Subtype.val ⁻¹' incrementsGlobalRelativeSupport W (fun z => g.eta l q z*g.cutoff l z) := by
      cases ch with
      | false => exact (hr l q).2.2.2.2.2
      | true => exact (hr l q).2.2.2.2.1
    exact hbase.trans (fun z hz => raw.hPrimarySupport l (hcut hz))
  exact ⟨contMDiffOn_finsetSum (fun q _ => hext q),
    actualRepairModelFirstDefect_finite_sum_support _ _ hs⟩

theorem actualRepairModelFirstDefect_prescribed_amplitude_regular
    (imag : Bool) (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Ep → D → M) (chi : X → ℝ)
    (nu : (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c b x))
    (a : OpenPartialHomeomorph (Ep × M) X) (W K : Set (Ep × M)) (hW : IsOpen W)
    (n j length : ℕ) (ell Mg Bchi Bnu tau delta weight : ℝ)
    (raw : ActualPrescribedSpatialRawProfiles F hF c chi nu a W K n j ell Mg Bchi Bnu)
    (u : Fin p → ℝ) :
    let vf := actualProbeNormalAmplitude F c chi nu delta tau weight
    let amplitude := round4PrescribedGlobalAmplitude imag label l F hF c vf tau length a u
    ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,V) ∞ amplitude W ∧
      tsupport (fun z : W => amplitude z) ⊆ Subtype.val ⁻¹' K := by
  intro vf amplitude
  have hvf : ContDiffOn ℝ ∞ (fun z : X => (vf z.1 z.2 : V)) a.target :=
    (raw.cutoff_smooth.smul raw.normal_smooth).const_smul (-(delta*tau)/weight^2)
  have hinput : ∀ z ∈ a.target, z ∈ tsupport (fun w : X => (vf w.1 w.2 : V)) → a.symm z ∈ K := by
    intro z hz hn
    exact raw.cutoff_support z hz (((tsupport_smul_subset_right _ _).trans (tsupport_smul_subset_left _ _)) hn)
  exact round4_prescribed_global_amplitude_smooth imag label l F hF c vf tau length a W K
    hW raw.closed_support raw.support_source raw.chart_smooth raw.A_smooth raw.B_smooth raw.G_smooth
    raw.J_smooth raw.T_smooth raw.BR_smooth hvf hinput u

theorem actualRepairModelFirstDefect_common_amplitude_regular
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (label : (Fin r × Bool) ↪ Fin p)
    (c : Fin r → Ep → D → M) (chi : Fin r → X → ℝ)
    (nu : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (input : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (W : Set (Ep × M)) (K : (Λ ⊕ Fin r) → Set (Ep × M))
    (background : ParameterRound2GlobalMeanPrimitives F hF g input W (fun l => K (Sum.inl l)))
    (n j backgroundLength probeLength : ℕ) (ell Mg Bchi Bnu tau delta : ℝ) (weight : Fin r → ℝ)
    (prescribed : ∀ l, ActualPrescribedSpatialRawProfiles F hF (c l) (chi l) (nu l) (a l)
      W (K (Sum.inr l)) n j ell Mg Bchi Bnu)
    (u : Fin p → ℝ) :
    let vf := fun l => actualProbeNormalAmplitude F (c l) (chi l) (nu l) delta tau (weight l)
    let amplitude := round4ParameterProbeCombinedAmplitude F hF g label c vf tau delta backgroundLength probeLength a input u
    ∀ ch l, ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,V) ∞ (amplitude ch l) W ∧
      tsupport (fun z : W => amplitude ch l z) ⊆ Subtype.val ⁻¹' K l := by
  intro vf amplitude ch l
  cases l with
  | inl l =>
    have hb := actualRepairModelFirstDefect_background_amplitude_regular F hF g input W
      (fun l => K (Sum.inl l)) background backgroundLength tau (!ch) l
    have hc : ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,ℝ) ∞ (fun _ : Ep × M => delta) W := contMDiffOn_const
    exact ⟨hc.smul hb.1,(tsupport_smul_subset_right _ _).trans hb.2⟩
  | inr l =>
    exact actualRepairModelFirstDefect_prescribed_amplitude_regular ch label l F hF (c l) (chi l) (nu l) (a l)
      W (K (Sum.inr l)) background.hW n j probeLength ell Mg Bchi Bnu tau delta (weight l) (prescribed l) u

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualRepairModelFirstDefect_common_amplitude_regular
