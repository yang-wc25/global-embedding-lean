import Probes.ActualIncrementOriginalPrimitiveBinding
import Probes.ActualSecondaryOriginalConstruction
import GlobalEmbedding.Paper.GoodCovectorRescaling

/-! Every nonzero ordered signed secondary phase is genuinely Good for the
original map on its actual original joint support pair. This includes the
negative and doubled records and differentiates their literal sine/cosine
phase functions. No Good hypothesis for an independently selected secondary
phase is added. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "𝓙" => 𝓘(ℝ,Es)

theorem actual_original_signed_secondary_phase_good
    (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) (z : P × M)
    (hz : z ∈ incrementsOriginalRelativeCutoffSupport Data r.val.1.1 ∩
      incrementsOriginalRelativeCutoffSupport Data r.val.1.2) :
    let psi := fun x : M =>
      ![Data.phase r.val.1.1 (z.1,x)+Data.phase r.val.1.2 (z.1,x),
        Data.phase r.val.1.1 (z.1,x)-Data.phase r.val.1.2 (z.1,x),
        -Data.phase r.val.1.1 (z.1,x)+Data.phase r.val.1.2 (z.1,x),
        -Data.phase r.val.1.1 (z.1,x)-Data.phase r.val.1.2 (z.1,x)] r.val.2
    GoodCovector (fun x => Data.F (z.1,x))
      (incrementsOriginal_slice_contMDiff Data hd hs z.1
        (incrementsOriginalRelativeCutoffSupport_subset Data r.val.1.1 hz.1).1) z.2
      ((tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi z.2)).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓘(ℝ,ℝ) psi z.2)) := by
  rcases r with ⟨⟨⟨nu,mu⟩,q⟩,hr⟩
  let F := fun x => Data.F (z.1,x)
  let hF := incrementsOriginal_slice_contMDiff Data hd hs z.1
    (incrementsOriginalRelativeCutoffSupport_subset Data nu hz.1).1
  let xi := incrementsOriginalPhaseCovector Data nu z.1 z.2
  let eta := incrementsOriginalPhaseCovector Data mu z.1 z.2
  have hnegMap (a : TangentSpace 𝓙 z.2 →L[ℝ] ℝ) : (-1 : ℝ) • a = -a := by
    ext v
    simp only [smul_apply,neg_apply,smul_eq_mul,neg_one_mul]
  have hnu : z ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data :=
    ⟨hd.cutoff_support_local nu hz.1,incrementsOriginalRelativeCutoffSupport_subset Data nu hz.1⟩
  have hmu : z ∈ Data.primaryDomain mu ∩ incrementsOriginalParameterRegion Data :=
    ⟨hd.cutoff_support_local mu hz.2,incrementsOriginalRelativeCutoffSupport_subset Data mu hz.2⟩
  have hplus : GoodCovector F hF z.2 (xi+eta) := by
    by_cases h : nu = mu
    · subst mu
      simpa only [xi,eta,two_smul] using hp.doubled_good nu z hnu
    · simpa [xi,eta,F] using hp.interaction_good nu mu h true z hz
  have hminus (h : nu ≠ mu) : GoodCovector F hF z.2 (xi-eta) := by
    simpa [xi,eta,F,sub_eq_add_neg,hnegMap] using hp.interaction_good nu mu h false z hz
  have hreverse (h : nu ≠ mu) : GoodCovector F hF z.2 (eta-xi) := by
    simpa [xi,eta,F,sub_eq_add_neg,hnegMap] using
      hp.interaction_good mu nu (Ne.symm h) false z ⟨hz.2,hz.1⟩
  have hneg : GoodCovector F hF z.2 (-(xi+eta)) := by
    simpa only [hnegMap] using
      (good_covector_smul_iff F hF z.2 (xi+eta) (-1) (by norm_num)).mpr hplus
  have hSum : mfderiv 𝓙 𝓘(ℝ,ℝ)
      (fun x => Data.phase nu (z.1,x)+Data.phase mu (z.1,x)) z.2 = xi+eta :=
    actual_original_phase_sum_covector Data hd hs nu mu z.1 z.2 hnu hmu
  have hSub : mfderiv 𝓙 𝓘(ℝ,ℝ)
      (fun x => Data.phase nu (z.1,x)-Data.phase mu (z.1,x)) z.2 = xi-eta :=
    actual_original_phase_sub_covector Data hd hs nu mu z.1 z.2 hnu hmu
  have hRev : mfderiv 𝓙 𝓘(ℝ,ℝ)
      (fun x => Data.phase mu (z.1,x)-Data.phase nu (z.1,x)) z.2 = eta-xi :=
    actual_original_phase_sub_covector Data hd hs mu nu z.1 z.2 hmu hnu
  fin_cases q
  · change GoodCovector F hF z.2 (mfderiv 𝓙 𝓘(ℝ,ℝ)
      (fun x => Data.phase nu (z.1,x)+Data.phase mu (z.1,x)) z.2)
    rwa [hSum]
  · have hne : nu ≠ mu := by simpa using hr
    change GoodCovector F hF z.2 (mfderiv 𝓙 𝓘(ℝ,ℝ)
      (fun x => Data.phase nu (z.1,x)-Data.phase mu (z.1,x)) z.2)
    rw [hSub]
    exact hminus hne
  · have hne : nu ≠ mu := by simpa using hr
    change GoodCovector F hF z.2 (mfderiv 𝓙 𝓘(ℝ,ℝ)
      (fun x => -Data.phase nu (z.1,x)+Data.phase mu (z.1,x)) z.2)
    have heq : (fun x => -Data.phase nu (z.1,x)+Data.phase mu (z.1,x)) =
        (fun x => Data.phase mu (z.1,x)-Data.phase nu (z.1,x)) := by funext x; ring
    rw [heq,hRev]
    exact hreverse hne
  · change GoodCovector F hF z.2 (mfderiv 𝓙 𝓘(ℝ,ℝ)
      (fun x => -Data.phase nu (z.1,x)-Data.phase mu (z.1,x)) z.2)
    have heq : (fun x => -Data.phase nu (z.1,x)-Data.phase mu (z.1,x)) =
        -(fun x => Data.phase nu (z.1,x)+Data.phase mu (z.1,x)) := by funext x; simp only [Pi.neg_apply]; ring
    rw [heq,mfderiv_neg,hSum]
    exact hneg

theorem actual_original_parameter_signed_secondary_phase_good
    (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) (z : Ep × M)
    (hz : ((Data.parameterChart i.2).symm z.1,z.2) ∈
      incrementsOriginalRelativeCutoffSupport Data r.val.1.1 ∩
        incrementsOriginalRelativeCutoffSupport Data r.val.1.2) :
    let p := (Data.parameterChart i.2).symm z.1
    let psi := fun x : M =>
      ![Data.phase r.val.1.1 (p,x)+Data.phase r.val.1.2 (p,x),
        Data.phase r.val.1.1 (p,x)-Data.phase r.val.1.2 (p,x),
        -Data.phase r.val.1.1 (p,x)+Data.phase r.val.1.2 (p,x),
        -Data.phase r.val.1.1 (p,x)-Data.phase r.val.1.2 (p,x)] r.val.2
    GoodCovector (actualOriginalOpenParameterSlice Data i z.1)
      (actualOriginalOpenParameterSlice_contMDiff Data hd hs i z.1) z.2
      ((tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi z.2)).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓘(ℝ,ℝ) psi z.2)) := by
  intro p psi
  have htrue := actual_original_signed_secondary_phase_good Data hd hs hp r (p,z.2) hz
  have htransport (f : M → EuclideanSpace ℝ (Fin N))
      (hf : ContMDiff 𝓙 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ f)
      (heq : f = fun x => Data.F (p,x)) :
      GoodCovector f hf z.2
        ((tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi z.2)).toContinuousLinearMap.comp
          (mfderiv 𝓙 𝓘(ℝ,ℝ) psi z.2)) := by
    subst f
    exact htrue
  exact htransport _ _ (actualOriginalOpenParameterSlice_eq Data i z.1
    (incrementsOriginalRelativeCutoffSupport_subset Data r.val.1.1 hz.1).1)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_signed_secondary_phase_good
#print axioms GlobalEmbedding.Continuation.actual_original_parameter_signed_secondary_phase_good
