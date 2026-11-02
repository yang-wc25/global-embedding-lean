import NormalPolar.PassiveWaveSeedObserverJets
import NormalPolar.PassiveWaveSeedNativeRaw
import NormalPolar.JointSecondaryGroupedProfiles

/-! Genuine grouped raw observation profiles in a true parameter chart.
The source and sample are the caller's actual original sets. The native
chart retains the parameter target, all original labels and all pieces;
only its identity parameter block adds one to the transition budget. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold Filter GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {S P Ep M : Type*} {m N r : ℕ}
  [NormedAddCommGroup S] [NormedSpace ℝ S] [Subsingleton S]
  [TopologicalSpace P] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  {Sub : Fin r → Type*} [∀ l, Fintype (Sub l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

def passiveWaveSeed_observation
    (B : OpenPartialHomeomorph P Ep) (e : OpenPartialHomeomorph M D)
    (F : S → M → V) (hF : ∀ s, ContMDiff IM 𝓘(ℝ,V) ∞ (F s))
    (c : (l : Fin r) → Sub l → S → D → M)
    (chi : (l : Fin r) → Sub l → S × D → ℝ)
    (nu : (l : Fin r) → (s : Sub l) → (b : S) → (x : D) →
      normalSpace (I := IM) (F b) (c l s b x))
    (a : (l : Fin r) → Sub l → OpenPartialHomeomorph (S × M) (S × D))
    (W : Set (S × M)) (K : (l : Fin r) → Sub l → Set (S × M))
    (n j : ℕ) (ell Mg Bchi Bnu : ℝ) (hell : 0 ≤ ell)
    (Omega Sample : Set (S × D)) (hSO : Sample ⊆ Omega)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (phase : Fin r → S × M → ℝ) (Mphase : ℝ)
    (profiles : JointGroupedPrescribedObservationProfiles F hF c chi nu a W K
      n j ell Mg Bchi Bnu (fun z : S × D => (z.1,e.symm z.2))
      Omega Sample T phase Mphase)
    (Sn : Set (Ep × D)) (hSnB : ∀ z ∈ Sn, z.1 ∈ B.target)
    (hSn : ∀ z ∈ Sn, (0,z.2) ∈ Sample) :
    JointGroupedPrescribedObservationProfiles
      (fun _ : Ep => F 0) (fun _ => hF 0) (fun l s _ => c l s 0)
      (fun l s (z : Ep × D) => chi l s (0,z.2)) (fun l s _ => nu l s 0)
      (fun l s => round3ParameterChartPullback B (passiveParameterChart 0 (a l s)))
      {z : Ep × M | z.1 ∈ B.target ∧ (0,z.2) ∈ W}
      (fun l s => {z : Ep × M | z.1 ∈ B.target ∧ (0,z.2) ∈ K l s})
      n j ell Mg Bchi Bnu (fun z : Ep × D => (z.1,e.symm z.2))
      {z : Ep × D | z.1 ∈ B.target ∧ (0,z.2) ∈ Omega}
      Sn (fun k => 1+T k) (fun l (z : Ep × M) => phase l (0,z.2)) Mphase := by
  let L : (Ep × D) →L[ℝ] (S × D) := passiveParameterProjection
  let dom (l : Fin r) (s : Sub l) : Set (Ep × D) :=
    {z | z.1 ∈ B.target ∧ (0,z.2) ∈ profiles.domains l s}
  have hopen (l : Fin r) (s : Sub l) : IsOpen (dom l s) :=
    (B.open_target.preimage continuous_fst).inter
      ((profiles.domains_open l s).preimage L.continuous)
  have heq (l : Fin r) (s : Sub l) :
      EqOn (round3ParameterChartPullback B (passiveParameterChart 0 (a l s)) ∘
        (fun z : Ep × D => (z.1,e.symm z.2)))
      (fun z : Ep × D => (z.1,((a l s) (0,e.symm z.2)).2)) (dom l s) := by
    intro z hz
    rw [Function.comp_apply,passiveWaveSeed_native_apply 0 B (a l s)
      (z.1,e.symm z.2) hz.1]
    rfl
  have hdom (l : Fin r) (s : Sub l) (z : Ep × D)
      (hz : z ∈ Sn ∩ (fun z : Ep × D => (z.1,e.symm z.2)) ⁻¹'
        {z : Ep × M | z.1 ∈ B.target ∧ (0,z.2) ∈ K l s}) :
      z ∈ dom l s :=
    ⟨hSnB z hz.1,profiles.active_domain l s ⟨hSO (hSn z hz.1),hz.2.2⟩⟩
  refine {
    raw := fun l s => passiveWaveSeed_native_raw B F hF (c l s) (chi l s) (nu l s)
      (a l s) W (K l s) n j ell Mg Bchi Bnu (profiles.raw l s)
    domains := dom
    domains_open := hopen
    active_domain := fun l s z hz => ⟨hz.1.1,profiles.active_domain l s ⟨hz.1.2,hz.2.2⟩⟩
    source := fun l s z hz => (passiveWaveSeed_native_source 0 B (a l s)
      (z.1,e.symm z.2)).mpr ⟨hz.1,profiles.source l s hz.2⟩
    transition_smooth := ?_
    sample := ?_
    transition_jets := ?_
    phase_smooth := fun l s => ((profiles.phase_smooth l s).comp_continuousLinearMap L).mono
      (fun _ hz => hz.2)
    phase_jets := ?_ }
  · intro l s
    have hh : ContDiffOn ℝ ∞ (fun z : Ep × D =>
        (z.1,((a l s) (0,e.symm z.2)).2)) (L ⁻¹' profiles.domains l s) :=
      contDiffOn_fst.prodMk ((profiles.transition_smooth l s).snd.comp_continuousLinearMap L)
    exact (hh.mono (fun _ hz => hz.2)).congr (heq l s)
  · intro l s z hz
    rw [passiveWaveSeed_native_apply 0 B (a l s) (z.1,e.symm z.2) (hSnB z hz.1)]
    change z.1 ∈ B.target ∧ (0,((a l s) (0,e.symm z.2)).2) ∈ (profiles.raw l s).sample
    refine ⟨hSnB z hz.1,?_⟩
    have he : (0,((a l s) (0,e.symm z.2)).2) = (a l s) (0,e.symm z.2) :=
      Prod.ext (Subsingleton.elim _ _) rfl
    rw [he]
    exact profiles.sample l s (0,z.2) ⟨hSn z hz.1,hz.2.2⟩
  · intro l s k hk hkj z hz
    rw [((heq l s).eventuallyEq_of_mem ((hopen l s).mem_nhds (hdom l s z hz))).iteratedFDeriv ℝ k |>.eq_of_nhds]
    exact passiveWaveSeed_transition_jets
      ((a l s) ∘ (fun y : S × D => (y.1,e.symm y.2))) (profiles.domains l s)
      (profiles.domains_open l s) (profiles.transition_smooth l s) z (hdom l s z hz).2
      ell hell k hk (T k) (hT k)
      (profiles.transition_jets l s k hk hkj (0,z.2) ⟨hSn z hz.1,hz.2.2⟩)
  · intro l s k hkj z hz
    change ell^k * ‖iteratedFDeriv ℝ (k+1)
      (fun w : Ep × D => (phase l ∘ (fun y : S × D => (y.1,e.symm y.2))) (0,w.2)) z‖ ≤ Mphase
    rw [passiveParameter_iteratedFDeriv_norm (0 : S)
      (phase l ∘ (fun y : S × D => (y.1,e.symm y.2))) (profiles.domains l s)
      (profiles.domains_open l s) (profiles.phase_smooth l s) z (hdom l s z hz).2
      (k+1) (by simp)]
    exact profiles.phase_jets l s k hkj (0,z.2) ⟨hSn z hz.1,hz.2.2⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveWaveSeed_observation
