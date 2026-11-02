import GlobalEmbedding.Offline.CoincidenceDifferentialRank
import GlobalEmbedding.Offline.PairedValueCoincidenceRank

/-!
Internal normed packaging for the supported incidence. The range inequality
and finite-frame margin are the previously accepted consumers. This file only
keeps their finite synthesis and actual preimages stable while the rank-q
branch uses a separate algebraic representation of its quotient carriers.
-/

noncomputable section
open Module
open scoped BigOperators

namespace GlobalEmbedding.Upgrade

variable {E P V W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

def incidenceFiniteSynthesis {ι : Type*} [Fintype ι] (c : ι → V) :
    (ι → ℝ) →L[ℝ] V :=
  LinearMap.toContinuousLinearMap (Fintype.linearCombination ℝ c)

@[simp] theorem incidenceFiniteSynthesis_apply {ι : Type*} [Fintype ι]
    (c : ι → V) (t : ι → ℝ) : incidenceFiniteSynthesis c t = ∑ i, t i • c i :=
  Fintype.linearCombination_apply ℝ c t

theorem incidenceFiniteSynthesis_projected_range {ι : Type*} [Fintype ι]
    (c : ι → V) (Q : V →L[ℝ] W) :
    (Q.comp (incidenceFiniteSynthesis c)).range = Submodule.span ℝ (Set.range (Q ∘ c)) := by
  change (Q.toLinearMap.comp (Fintype.linearCombination ℝ c)).range = _
  rw [LinearMap.range_comp, Fintype.range_linearCombination, Submodule.map_span,
    ← Set.range_comp]
  rfl

theorem incidencePrincipalCoprod_finrank (P0 : P →L[ℝ] V) (T : E →L[ℝ] V)
    (Q : V →L[ℝ] W) (hT : Function.Injective T) (hQT : Q.comp T = 0) :
    finrank ℝ E + finrank ℝ (Q.comp P0).range ≤ finrank ℝ (P0.coprod T).range := by
  have hTJ : T.toLinearMap.range ≤ (P0.coprod T).toLinearMap.range := by
    rintro _ ⟨v, rfl⟩
    exact ⟨(0, v), by simp⟩
  have hPJ : P0.toLinearMap.range ≤ (P0.coprod T).toLinearMap.range := by
    rintro _ ⟨p, rfl⟩
    exact ⟨(p, 0), by simp⟩
  exact Offline.finrank_joint_range_ge_tangent_add_projected_parameter
    (P0.coprod T).toLinearMap T.toLinearMap P0.toLinearMap Q.toLinearMap
    hT hTJ hPJ (congrArg ContinuousLinearMap.toLinearMap hQT)

theorem incidenceFiniteFrame_of_rank (J : P →L[ℝ] V) (k : ℕ)
    (hdim : k ≤ finrank ℝ J.range) :
    ∃ d : Fin k → P, LinearIndependent ℝ (fun i ↦ J (d i)) ∧
      ∃ margin : ℝ, 0 < margin ∧ ∀ c : Fin k → ℝ,
        margin * ‖c‖ ≤ ‖∑ i, c i • J (d i)‖ := by
  classical
  let b := Module.finBasis ℝ J.range
  let e : Fin k → Fin (finrank ℝ J.range) := Fin.castLE hdim
  have he : Function.Injective e := Fin.castLE_injective hdim
  have hli : LinearIndependent ℝ (fun i : Fin k ↦ (b (e i) : V)) :=
    (b.linearIndependent.comp e he).map' J.range.subtype (by simp)
  have hex : ∀ i : Fin k, ∃ d : P, J d = (b (e i) : V) :=
    fun i ↦ (b (e i)).property
  choose d hd using hex
  have hdli : LinearIndependent ℝ (fun i ↦ J (d i)) := by
    simpa only [hd] using hli
  obtain ⟨margin, hm, hbound⟩ := Offline.exists_positive_finite_frame_margin
    (fun i ↦ J (d i)) hdli
  exact ⟨d, hdli, margin, hm, hbound⟩

end GlobalEmbedding.Upgrade
