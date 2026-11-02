import NormalPolar.JointSecondaryOriginalMixedData

/-! Choose the prescribed weights from the actual original Data and legal
waves. Background exponent zero leaves every original background phase
unchanged. Original background interactions are retained; every genuine
mixed and prescribed interaction is constructed by the compact hierarchy. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.Upgrade
open Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N r : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "IM" => 𝓘(ℝ,D)
variable (Data : IncrementsOriginalNativeData (m+1) d N M P)
  (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
  (p : P) (hpO : p ∈ Data.parameterOpen)
  (waves : Fin r → LocalLegalWave (n := m+1) (fun x => Data.F (p,x))
    (incrementsOriginal_slice_contMDiff Data hd hs p hpO))

theorem jointSecondary_original_mixed_signed_good
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data) :
    ∃ A : ℝ, 1 < A ∧
      ∀ rec : ActualSecondarySignedRecord (Fin Data.primaryCount ⊕ Fin r), ∀ x,
      x ∈ jointSecondaryOriginalMixedCarrier Data hd hs p hpO waves rec.val.1.1 ∩
        jointSecondaryOriginalMixedCarrier Data hd hs p hpO waves rec.val.1.2 →
      GoodCovector (fun y => Data.F (p,y)) (incrementsOriginal_slice_contMDiff Data hd hs p hpO) x
        (mfderiv IM 𝓘(ℝ,ℝ)
          (jointSecondarySpatialSignedPhase (jointSecondaryOriginalMixedPhase Data hd hs p hpO waves A) rec.val) x) := by
  let F : M → EuclideanSpace ℝ (Fin N) := fun y => Data.F (p,y)
  let hF := incrementsOriginal_slice_contMDiff Data hd hs p hpO
  let K := jointSecondaryOriginalMixedCarrier Data hd hs p hpO waves
  let O := jointSecondaryOriginalMixedDomain Data hd hs p hpO waves
  let phi := jointSecondaryOriginalMixedUnweightedPhase Data hd hs p hpO waves
  let label := jointSecondaryOriginalMixedExponent (r := r) Data
  obtain ⟨A,hA,hprimary,hdoubled,hweighted⟩ :=
    jointSecondary_original_compact_phase_weights F hF (hImm.immersion p hpO) phi K O
      (jointSecondaryOriginalMixedCarrier_closed Data hd hs p hpO waves)
      (jointSecondaryOriginalMixedDomain_open Data hd hs p hpO waves)
      (jointSecondaryOriginalMixedCarrier_domain Data hd hs p hpO waves)
      (jointSecondaryOriginalMixedUnweightedPhase_smooth Data hd hs p hpO waves)
      (jointSecondaryOriginalMixedUnweightedPhase_good Data hd hs p hpO waves hp) label
  let phase := jointSecondaryOriginalMixedPhase Data hd hs p hpO waves A
  have hcoef (l : Fin Data.primaryCount ⊕ Fin r) (x : M) (hx : x ∈ K l) :
      jointSecondaryPhaseCovector (m := m) (phase l) x =
        A^(label l) • jointSecondaryPhaseCovector (m := m) (phi l) x :=
    jointSecondaryOriginalMixedPhase_covector Data hd hs p hpO waves A l x
      (jointSecondaryOriginalMixedCarrier_domain Data hd hs p hpO waves l hx)
  have hdouble (l : Fin Data.primaryCount ⊕ Fin r) (x : M) (hx : x ∈ K l) :
      GoodCovector F hF x (jointSecondaryPhaseCovector (m := m) (phase l) x +
        jointSecondaryPhaseCovector (m := m) (phase l) x) := by
    have h := hdoubled l x hx
    rw [← hcoef l x hx] at h
    have heq : (2:ℝ) • jointSecondaryPhaseCovector (m := m) (phase l) x =
        jointSecondaryPhaseCovector (m := m) (phase l) x +
          jointSecondaryPhaseCovector (m := m) (phase l) x := by
      ext v
      simp only [smul_apply,add_apply,smul_eq_mul]
      ring
    rwa [heq] at h
  have hpair (l l' : Fin Data.primaryCount ⊕ Fin r) (x : M) (hx : x ∈ K l ∩ K l')
      (hne : label l ≠ label l') :
      GoodCovector F hF x (jointSecondaryPhaseCovector (m := m) (phase l) x +
        jointSecondaryPhaseCovector (m := m) (phase l') x) ∧
      GoodCovector F hF x (jointSecondaryPhaseCovector (m := m) (phase l) x -
        jointSecondaryPhaseCovector (m := m) (phase l') x) := by
    have h := hweighted l l' x hx hne
    rw [← hcoef l x hx.1,← hcoef l' x hx.2] at h
    exact h
  have hall (l l' : Fin Data.primaryCount ⊕ Fin r) (x : M) (hx : x ∈ K l ∩ K l') :
      GoodCovector F hF x (jointSecondaryPhaseCovector (m := m) (phase l) x +
        jointSecondaryPhaseCovector (m := m) (phase l') x) ∧
      (l ≠ l' → GoodCovector F hF x (jointSecondaryPhaseCovector (m := m) (phase l) x -
        jointSecondaryPhaseCovector (m := m) (phase l') x)) := by
    by_cases heq : l = l'
    · subst l'
      exact ⟨hdouble l x hx.1,fun h => False.elim (h rfl)⟩
    · cases l with
      | inl nu =>
        cases l' with
        | inl mu =>
          have hne : nu ≠ mu := fun h => heq (congrArg Sum.inl h)
          have hpplus := hp.interaction_good nu mu hne true (p,x) hx
          have hpminus := hp.interaction_good nu mu hne false (p,x) hx
          have hneg (a : TangentSpace IM x →L[ℝ] ℝ) : (-1:ℝ) • a = -a := by
            ext v
            simp only [smul_apply,neg_apply,smul_eq_mul,neg_one_mul]
          refine ⟨?_,fun _ => ?_⟩
          · simpa only [Bool.true_eq,ite_true,one_smul,F,phase,jointSecondaryOriginalMixedPhase,
              Sum.elim_inl,jointSecondaryPhaseCovector,incrementsOriginalPhaseCovector] using hpplus
          · simpa only [Bool.false_eq_true,ite_false,hneg,sub_eq_add_neg,F,phase,
              jointSecondaryOriginalMixedPhase,Sum.elim_inl,jointSecondaryPhaseCovector,
              incrementsOriginalPhaseCovector] using hpminus
        | inr k =>
          have h := hpair (Sum.inl nu) (Sum.inr k) x hx
            (by simp [label,jointSecondaryOriginalMixedExponent])
          exact ⟨h.1,fun _ => h.2⟩
      | inr k =>
        cases l' with
        | inl nu =>
          have h := hpair (Sum.inr k) (Sum.inl nu) x hx
            (by simp [label,jointSecondaryOriginalMixedExponent])
          exact ⟨h.1,fun _ => h.2⟩
        | inr k' =>
          have hval : k.val ≠ k'.val := fun h => heq (congrArg Sum.inr (Fin.ext h))
          have hne : label (Sum.inr k) ≠ label (Sum.inr k') := by
            change k.val+1 ≠ k'.val+1
            omega
          have h := hpair (Sum.inr k) (Sum.inr k') x hx hne
          exact ⟨h.1,fun _ => h.2⟩
  refine ⟨A,hA,?_⟩
  intro rec x hx
  have hdiff (l : Fin Data.primaryCount ⊕ Fin r) (hx : x ∈ K l) :
      MDifferentiableAt IM 𝓘(ℝ,ℝ) (phase l) x :=
    ((jointSecondaryOriginalMixedPhase_smooth Data hd hs p hpO waves A l).contMDiffAt
      ((jointSecondaryOriginalMixedDomain_open Data hd hs p hpO waves l).mem_nhds
        (jointSecondaryOriginalMixedCarrier_domain Data hd hs p hpO waves l hx))).mdifferentiableAt (by simp)
  exact jointSecondarySpatialSignedPhase_good F hF phase rec x
    (hdiff _ hx.1) (hdiff _ hx.2) (hall _ _ x hx).1 (hall _ _ x hx).2

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondary_original_mixed_signed_good
