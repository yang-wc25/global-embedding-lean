import NormalPolar.PassiveRescaledData

/-! Original primary, doubled and genuinely interacting Good covectors,
and the same given free normals, survive the actual nonzero contraction.
All pair carriers and original kernels remain literal. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

theorem passiveRescaledData_phase_conditions (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs) (c : ℝ) (hc : c ≠ 0) :
    IncrementsOriginalPhaseConditions (passiveRescaledData Data c)
      (passiveRescaledData_domains Data hd c) (passiveRescaledData_smooth Data hs c) := by
  constructor
  · intro nu z hz
    exact (goodCovector_const_rescale_iff (fun x => Data.F (z.1,x))
      (incrementsOriginal_slice_contMDiff Data hd hs z.1 hz.2.1) c hc z.2 _).mpr
        (hp.primary_good nu z hz)
  · intro nu z hz
    exact (goodCovector_const_rescale_iff (fun x => Data.F (z.1,x))
      (incrementsOriginal_slice_contMDiff Data hd hs z.1 hz.2.1) c hc z.2 _).mpr
        (hp.doubled_good nu z hz)
  · intro nu mu hnu sign z hz
    exact (goodCovector_const_rescale_iff (fun x => Data.F (z.1,x))
      (incrementsOriginal_slice_contMDiff Data hd hs z.1
        ((incrementsOriginalRelativeCutoffSupport_subset Data nu hz.1).1)) c hc z.2 _).mpr
        (hp.interaction_good nu mu hnu sign z hz)

theorem passiveRescaledData_free_normals (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs) (c : ℝ) (hc : c ≠ 0) :
    IncrementsOriginalFreeNormalConditions (passiveRescaledData Data c)
      (passiveRescaledData_domains Data hd c) (passiveRescaledData_smooth Data hs c) := by
  refine ⟨hn.unit,?_,?_⟩
  · intro nu z hz
    change Data.freeNormal nu z ∈ normalSpace (I := IM) (c • (fun x => Data.F (z.1,x))) z.2
    rw [normalSpace_const_rescale (fun x => Data.F (z.1,x))
      (incrementsOriginal_slice_contMDiff Data hd hs z.1 hz.2.1) c hc]
    exact hn.normal nu z hz
  · intro nu z hz u v
    let F := fun x => Data.F (z.1,x)
    let hF := incrementsOriginal_slice_contMDiff Data hd hs z.1 hz.2.1
    have hb := DFunLike.congr_fun (trueSecondForm_const_rescale F hF c hc z.2)
      (symmetricSquareProduct (TangentSpace IM z.2) u.val v.val)
    change (trueSecondForm (c • F) (contMDiff_const_rescale F hF c) z.2
      (symmetricSquareProduct (TangentSpace IM z.2) u.val v.val) : V) =
      c • (trueSecondForm F hF z.2
        (symmetricSquareProduct (TangentSpace IM z.2) u.val v.val) : V) at hb
    change inner ℝ (trueSecondForm (c • F) (contMDiff_const_rescale F hF c) z.2
      (symmetricSquareProduct (TangentSpace IM z.2) u.val v.val) : V) (Data.freeNormal nu z) = 0
    rw [hb,real_inner_smul_left,hn.free nu z hz u v,mul_zero]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.passiveRescaledData_phase_conditions
#print axioms GlobalEmbedding.Continuation.passiveRescaledData_free_normals
