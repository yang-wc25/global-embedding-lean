import GlobalEmbedding.Paper.IncrementsJointActualGeometry
import GlobalEmbedding.Paper.IncrementsChosenTransverseCompactWitness
import Probes.ActualIncrementGoodPhaseGeometry
import Probes.ActualIncrementPhysicalChartRows

/-! Compact conditioning for the actual chosen phase coordinates. The same
first frame and true transverse columns receive positive reserves from original
immersion and Good. These constants depend on the actual compact family;
no claim of a uniform-before-data template constant is made here. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ, D)
local notation "P" => {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
local notation "Tdata" => EuclideanSpace ℝ P
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) M]

theorem actual_increment_joint_compact_reserves
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    (e : Ep → OpenPartialHomeomorph M D)
    (he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (ψ : Ep → M → ℝ) (U : Set (Ep × M)) (O : Set (Ep × D)) (hO : IsOpen O)
    (hFjoint : ContMDiffOn ((𝓘(ℝ, Ep)).prod 𝓙) 𝓘(ℝ, V) ∞ (Function.uncurry F) U)
    (hψjoint : ContMDiffOn ((𝓘(ℝ, Ep)).prod 𝓙) 𝓘(ℝ, ℝ) ∞ (Function.uncurry ψ) U)
    (hcjoint : ContMDiffOn 𝓘(ℝ, Ep × D) 𝓙 ∞ (fun z ↦ (e z.1).symm z.2) O)
    (hcoord : ∀ z ∈ O, z.2 ∈ (e z.1).target)
    (hmap : MapsTo (fun z : Ep × D ↦ (z.1, (e z.1).symm z.2)) O U)
    (hU : IsOpen U)
    (hinj : ∀ z ∈ O, Function.Injective
      (mfderiv 𝓙 𝓘(ℝ, V) (F z.1) ((e z.1).symm z.2)))
    (hadapt : ∀ z ∈ O, ψ z.1 ((e z.1).symm z.2) = z.2 0)
    (hgood : ∀ z ∈ O, GoodCovector (F z.1) (hF z.1) ((e z.1).symm z.2)
      ((tangentSpaceCastModel 𝓘(ℝ, ℝ) (ψ z.1 ((e z.1).symm z.2))).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓘(ℝ, ℝ) (ψ z.1) ((e z.1).symm z.2))))
    (K : Set (Ep × D)) (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ cF cT : ℝ, 0 < cF ∧ 0 < cT ∧
      (∀ z ∈ K, ∀ v : D,
        cF * ‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2 v‖^2) ∧
      ∀ z ∈ K, ∀ v : Tdata,
        cT * ‖v‖^2 ≤
          ‖incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (e z.1).symm z.2 v‖^2 := by
  obtain ⟨hFirst,hSecond,hG,hN,hB,hJ,hT,hA,hC,hAC,hBC⟩ :=
    incrementsJointActualGeometry_contDiffOn F hF e he ψ U O hO hFjoint hψjoint
      hcjoint hcoord hmap hU hinj hadapt hgood
  let first := fun z : Ep × D => fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2
  have hFirstInj (z : Ep × D) (hz : z ∈ O) : Function.Injective (first z) :=
    actual_increment_chart_derivative_injective (F z.1) (hF z.1) (e z.1) (he z.1)
      z.2 (hcoord z hz) (hinj z hz)
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hFirstK : Continuous (fun z : K => first z) :=
    (hFirst.continuousOn.mono hKO).domRestrict
  obtain ⟨cF,hcF,hFb⟩ := free_compact_frame_lower_bound
    (fun z : K => first z) hFirstK (fun z => hFirstInj z (hKO z.property))
  have hFrame : ContDiffOn ℝ ∞ (fun z : Ep × D =>
      incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (e z.1).symm z.2) O := by
    apply contDiffOn_clm_apply.mpr
    intro t
    have hh : ContDiffOn ℝ ∞ (fun z : Ep × D => ∑ q : P,
        t q • (incrementsModeSecondForm (F z.1) (hF z.1) (e z.1).symm z.2
          q.val.1.succ q.val.2.succ : V)) O :=
      ContDiffOn.sum fun q _ => (hB q.val.1.succ q.val.2.succ).const_smul (t q)
    simpa [incrementsModeAmbientTransverseFrame] using hh
  have hFrameInj (z : Ep × D) (hz : z ∈ O) : Function.Injective
      (incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (e z.1).symm z.2) := by
    have hslice : IsOpen {x : D | (z.1,x) ∈ O} :=
      hO.preimage (continuous_const.prodMk continuous_id)
    have hpsi : MDifferentiableAt 𝓙 𝓘(ℝ, ℝ) (ψ z.1) ((e z.1).symm z.2) := by
      have hh := (hψjoint.contMDiffAt (hU.mem_nhds (hmap hz))).comp
        ((e z.1).symm z.2) (contMDiffAt_const.prodMk contMDiffAt_id)
      exact hh.mdifferentiableAt (by simp)
    have hg := actual_increment_transverse_gram_of_good_phase
      (F z.1) (hF z.1) (ψ z.1) (e z.1) (he z.1)
      {x : D | (z.1,x) ∈ O} hslice (fun x hx => hcoord (z.1,x) hx) z.2 hz hpsi
      (fun x hx => hadapt (z.1,x) hx) (hgood z hz)
    exact incrementsModeAmbientTransverseFrame_injective _ _ _ _ hg
  obtain ⟨cT,hcT,hTb⟩ := (increments_chosen_transverse_compact_coercivity_iff
    F hF (fun p => (e p).symm) K hK (hFrame.continuousOn.mono hKO)).mp
      (fun z hz => hFrameInj z (hKO hz))
  exact ⟨cF,cT,hcF,hcT,fun z hz v => hFb ⟨z,hz⟩ v,hTb⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_increment_joint_compact_reserves
