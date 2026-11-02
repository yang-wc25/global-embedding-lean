import Probes.ActualIncrementCompactReserves
import Probes.ActualCompactFrameOpenReserve

/-! Actual chosen first/transverse frames on a compact active carrier produce
one genuine open conditioning domain. There is no supplied numeric chosen
margin, inverse bound, or tangent Riemannian norm. These base constants depend
on the actual fixed packet; a data-uniform template bound is a separate gate. -/

noncomputable section
open GlobalEmbedding.Paper Manifold Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Pairs" => {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
local notation "Tdata" => EuclideanSpace ℝ Pairs
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

theorem actual_increment_joint_compact_open_reserves
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (e : Ep → OpenPartialHomeomorph M D)
    (he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (psi : Ep → M → ℝ) (W : Set (Ep × M)) (O : Set (Ep × D)) (hO : IsOpen O)
    (hFjoint : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞ (Function.uncurry F) W)
    (hpsi : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (Function.uncurry psi) W)
    (hcjoint : ContMDiffOn 𝓘(ℝ,Ep × D) 𝓙 ∞ (fun z => (e z.1).symm z.2) O)
    (hcoord : ∀ z ∈ O, z.2 ∈ (e z.1).target)
    (hmap : MapsTo (fun z : Ep × D => (z.1,(e z.1).symm z.2)) O W)
    (hW : IsOpen W)
    (hinj : ∀ z ∈ O, Function.Injective
      (mfderiv 𝓙 𝓘(ℝ,V) (F z.1) ((e z.1).symm z.2)))
    (hadapt : ∀ z ∈ O, psi z.1 ((e z.1).symm z.2) = z.2 0)
    (hgood : ∀ z ∈ O, GoodCovector (F z.1) (hF z.1) ((e z.1).symm z.2)
      ((tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi z.1 ((e z.1).symm z.2))).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓘(ℝ,ℝ) (psi z.1) ((e z.1).symm z.2))))
    (K : Set (Ep × D)) (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ (cF cT : ℝ) (O0 : Set (Ep × D)), 0 < cF ∧ 0 < cT ∧
      IsOpen O0 ∧ K ⊆ O0 ∧ O0 ⊆ O ∧
      (∀ z ∈ O0, ∀ v : D,
        cF*‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2 v‖^2) ∧
      ∀ z ∈ O0, ∀ v : Tdata,
        cT*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame
          (F z.1) (hF z.1) (e z.1).symm z.2 v‖^2 := by
  obtain ⟨cF0,cT0,hcF0,hcT0,hF0,hT0⟩ := actual_increment_joint_compact_reserves
    F hF e he psi W O hO hFjoint hpsi hcjoint hcoord hmap hW hinj hadapt hgood K hK hKO
  obtain ⟨hFirst,hSecond,hG,hN,hB,hJ,hT,hA,hC,hAC,hBC⟩ :=
    incrementsJointActualGeometry_contDiffOn F hF e he psi W O hO hFjoint hpsi
      hcjoint hcoord hmap hW hinj hadapt hgood
  let first := fun z : Ep × D => fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2
  let frame := fun z : Ep × D => incrementsModeAmbientTransverseFrame
    (F z.1) (hF z.1) (e z.1).symm z.2
  have hFrame : ContDiffOn ℝ ∞ frame O := by
    apply contDiffOn_clm_apply.mpr
    intro t
    have hh : ContDiffOn ℝ ∞ (fun z : Ep × D => ∑ q : Pairs,
        t q • (incrementsModeSecondForm (F z.1) (hF z.1) (e z.1).symm z.2
          q.val.1.succ q.val.2.succ : V)) O :=
      ContDiffOn.sum fun q _ => (hB q.val.1.succ q.val.2.succ).const_smul (t q)
    simpa [frame,incrementsModeAmbientTransverseFrame] using hh
  have injective_of_bound {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      (A : E →L[ℝ] V) (c : ℝ) (hc : 0 < c)
      (hb : ∀ v, c*‖v‖^2 ≤ ‖A v‖^2) : Function.Injective A := by
    apply (injective_iff_map_eq_zero A).mpr
    intro v hv
    have hh := hb v
    rw [hv,norm_zero,zero_pow (by norm_num)] at hh
    have hs : ‖v‖^2 ≤ 0 := (mul_le_mul_iff_right₀ hc).mp (by simpa using hh)
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg v])
  obtain ⟨cF,OF,hcF,hOF,hKOF,hOFO,hFb⟩ := actual_compact_frame_open_reserve
    first O K hO hK hKO hFirst.continuousOn
      (fun z hz => injective_of_bound (first z) cF0 hcF0 (hF0 z hz))
  obtain ⟨cT,OT,hcT,hOT,hKOT,hOTO,hTb⟩ := actual_compact_frame_open_reserve
    frame O K hO hK hKO hFrame.continuousOn
      (fun z hz => injective_of_bound (frame z) cT0 hcT0 (hT0 z hz))
  exact ⟨cF,cT,OF ∩ OT,hcF,hcT,hOF.inter hOT,
    fun _ hz => ⟨hKOF hz,hKOT hz⟩,fun _ hz => hOFO hz.1,
    fun z hz => hFb z hz.1,fun z hz => hTb z hz.2⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_increment_joint_compact_open_reserves
