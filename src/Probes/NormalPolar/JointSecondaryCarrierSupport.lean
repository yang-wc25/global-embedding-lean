import NormalPolar.JointSecondaryGroupedSupport

/-! Separate the true closed amplitude carrier from its open primitive
primary neighborhood. The actual extension support theorem first places
each subordinate amplitude inside its literal cutoff support; only then is
that support included in the desired carrier. No closed carrier is required
to be open, and the authoritative raw primary domains are unchanged. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open Set Function Manifold GlobalEmbedding.Paper
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N p r : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
  {Sub : Fin r → Type*} [∀ l, Fintype (Sub l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

theorem jointSecondary_background_amplitude_cutoff_support
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (W : Set (Ep × M)) (primaryDomain : Λ → Set (Ep × M))
    (raw : ParameterRound2GlobalMeanPrimitives F hF g input W primaryDomain)
    (length : ℕ) (tau : ℝ) :
    ∀ ch l, tsupport (fun z : W => incrementsGlobalPrimaryAmplitude F hF g input length tau ch l z) ⊆
      Subtype.val ⁻¹' incrementsGlobalRelativeSupport W (g.cutoff l) := by
  have hr := actual_global_primary_extension_regular F hF g input length tau W raw.hW
    primaryDomain raw.hPrimary raw.hPrimarySupport raw.hSourceW raw.hChart raw.hChartInv raw.hInverse
    raw.hCombinedSupport raw.hCut raw.hNormal raw.hArgument raw.hEta raw.hPositive
    raw.hG raw.hJ raw.hT0 raw.hA raw.hB raw.hSecond
  intro ch l
  apply actualRepairModelFirstDefect_finite_sum_support
  intro q
  have hcut : incrementsGlobalRelativeSupport W (fun z => g.eta l q z*g.cutoff l z) ⊆
      incrementsGlobalRelativeSupport W (g.cutoff l) := by
    rw [parameterRound2_global_relativeSupport_eq W raw.hW,parameterRound2_global_relativeSupport_eq W raw.hW]
    exact inter_subset_inter_right W tsupport_mul_subset_right
  have hbase : tsupport (fun z : W => incrementsGlobalPrimaryExtension F hF g input length tau ch l q z) ⊆
      Subtype.val ⁻¹' incrementsGlobalRelativeSupport W (fun z => g.eta l q z*g.cutoff l z) := by
    cases ch with
    | false => exact (hr l q).2.2.2.2.2
    | true => exact (hr l q).2.2.2.2.1
  exact hbase.trans (fun _ hz => hcut hz)

theorem jointGrouped_common_amplitude_carrier_support
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (label : (Fin r × Bool) ↪ Fin p)
    (c : (l : Fin r) → Sub l → Ep → D → M)
    (chi : (l : Fin r) → Sub l → X → ℝ)
    (nu : (l : Fin r) → (s : Sub l) → (b : Ep) → (x : D) →
      normalSpace (I := I) (F b) (c l s b x))
    (a : (l : Fin r) → Sub l → OpenPartialHomeomorph (Ep × M) X)
    (input : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (W : Set (Ep × M)) (primaryDomain : Λ → Set (Ep × M))
    (K : (Λ ⊕ Fin r) → Set (Ep × M))
    (pieceK : (l : Fin r) → Sub l → Set (Ep × M))
    (hpieceK : ∀ l s, pieceK l s ⊆ K (Sum.inr l))
    (background : ParameterRound2GlobalMeanPrimitives F hF g input W primaryDomain)
    (hbackground : ∀ l, incrementsGlobalRelativeSupport W (g.cutoff l) ⊆ K (Sum.inl l))
    (n j backgroundLength probeLength : ℕ) (ell Mg Bchi Bnu tau delta : ℝ) (weight : Fin r → ℝ)
    (prescribed : ∀ l s, ActualPrescribedSpatialRawProfiles F hF (c l s) (chi l s) (nu l s)
      (a l s) W (pieceK l s) n j ell Mg Bchi Bnu)
    (u : Ep → Fin p → ℝ) :
    let vf := fun l s => actualProbeNormalAmplitude F (c l s) (chi l s) (nu l s) delta tau (weight l)
    let amplitude := jointGroupedCombinedAmplitude F hF g label c vf tau delta
      backgroundLength probeLength a input u
    ∀ ch l, tsupport (fun z : W => amplitude ch l z.val) ⊆ Subtype.val ⁻¹' K l := by
  intro vf amplitude ch l
  cases l with
  | inl l =>
    exact (tsupport_smul_subset_right _ _).trans
      ((jointSecondary_background_amplitude_cutoff_support F hF g input W primaryDomain
        background backgroundLength tau (!ch) l).trans (fun _ hz => hbackground l hz))
  | inr l =>
    exact jointGroupedPrescribedAmplitude_variable_support ch label F hF c chi nu a
      W (fun l => K (Sum.inr l)) pieceK background.hW hpieceK n j probeLength
      ell Mg Bchi Bnu tau delta weight prescribed u l

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondary_background_amplitude_cutoff_support
#print axioms GlobalEmbedding.Continuation.jointGrouped_common_amplitude_carrier_support
