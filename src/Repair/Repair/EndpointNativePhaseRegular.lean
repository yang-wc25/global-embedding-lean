import Repair.EntrancePublic

/-! The original positive decomposition forces a nonzero cutoff at every
point.  Retaining the same primary phase conditions at the actual limit
therefore gives the repository's native PhaseRegular predicate everywhere. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Bundle Function
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IT" => 𝓘(ℝ,D)

theorem repair_decomposition_cutoff_cover
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Ref)
    (hMetric : Ref.H = fun p x => inducedMetric (I := IT) (fun y => Ref.F (p,y)) x)
    (hImm : IncrementsOriginalSliceImmersionInputs Ref)
    (p : P) (hp : p ∈ Ref.parameterOpen) (x : M) :
    ∃ nu, Ref.cutoff nu (p,x) ≠ 0 := by
  classical
  by_contra h
  have hz : ∀ nu, Ref.cutoff nu (p,x) = 0 := by simpa only [not_exists, not_not] using h
  have he := hDecomp.decomposition p hp x _ (hDecomp.H_mem p hp x)
  have he0 : Ref.H p x = 0 := by
    simpa only [incrementsOriginalDecompositionTensor,hz,zero_mul,zero_pow (by decide : 2 ≠ 0),
      zero_smul,Finset.sum_const_zero] using he
  letI : Nontrivial (TangentSpace IT x) := (tangentSpaceCastModel IT x).symm.injective.nontrivial
  obtain ⟨v,hv⟩ := exists_ne (0 : TangentSpace IT x)
  have hpos := inducedMetric_pos_of_injective_mfderiv (I := IT)
    (fun y => Ref.F (p,y)) x (hImm.immersion p hp x) hv
  have hv0 : inducedMetric (I := IT) (fun y => Ref.F (p,y)) x v v = 0 := by
    have := congrArg (fun A : LinearMap.BilinForm ℝ (TangentSpace IT x) => A v v) he0
    simpa only [hMetric, LinearMap.zero_apply] using this
  linarith

theorem repair_retained_original_phases_native_regular
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hAll : Ref.parameterSet = univ)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Ref)
    (hMetric : Ref.H = fun p x => inducedMetric (I := IT) (fun y => Ref.F (p,y)) x)
    (hImm : IncrementsOriginalSliceImmersionInputs Ref)
    (Fstar : P × M → V) (hFstar : ∀ p, ContMDiff IT 𝓘(ℝ,V) ∞ (fun x => Fstar (p,x)))
    (domain : Fin Ref.primaryCount → Set (P × M))
    (hSupport : ∀ nu, tsupport (Ref.cutoff nu) ⊆ domain nu)
    (hdE : IncrementsOriginalDomainConditions {Ref with F := Fstar, primaryDomain := domain})
    (hsE : IncrementsOriginalSmoothInputs {Ref with F := Fstar, primaryDomain := domain})
    (hpE : IncrementsOriginalPhaseConditions {Ref with F := Fstar, primaryDomain := domain} hdE hsE) :
    ∀ p, PhaseRegular (I := IT) (fun x => Fstar (p,x)) (hFstar p) := by
  intro p x
  have hp : p ∈ Ref.parameterOpen := hd.parameter_subset (by rw [hAll]; exact mem_univ p)
  obtain ⟨nu,hnu⟩ := repair_decomposition_cutoff_cover Ref hDecomp hMetric hImm p hp x
  have hSupp : (p,x) ∈ tsupport (Ref.cutoff nu) := subset_tsupport _ hnu
  have hg := hpE.primary_good nu (p,x) ⟨hSupport nu hSupp, hp, mem_univ x⟩
  exact ⟨_,hg⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_decomposition_cutoff_cover
#print axioms GlobalEmbedding.Continuation.repair_retained_original_phases_native_regular
