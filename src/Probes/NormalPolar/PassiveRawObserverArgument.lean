import NormalPolar.PassiveOriginalObserverCoordinates
import Smoothing.ParameterRound2MeanRawProfiles
import Smoothing.WeightedActualOperations

/-! The same produced raw background supplies the actual scalar argument in
an additional observer. The coordinate transition is the genuine e composed
with host inverse, and compact geometry produces its cost before the raw
input or scales. Both original L and input A participate in the estimate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M Tr Λ Β : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr] [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

def passiveRawObserverTransition (e host : OpenPartialHomeomorph M D) : X → X :=
  fun z => (z.1,e (host.symm z.2))

theorem passiveRawObserverTransition_smooth
    (e host : OpenPartialHomeomorph M D)
    (he : e ∈ maximalAtlas IM ∞ M) (hh : host ∈ maximalAtlas IM ∞ M) :
    ContDiffOn ℝ ∞ (passiveRawObserverTransition (d := d) e host)
      (passiveOriginalObserverDomain (OpenPartialHomeomorph.refl Ep) e host) := by
  have ht : ContDiffOn ℝ ∞ (e ∘ host.symm) (host.symm.trans e).source :=
    ((contMDiffOn_of_mem_maximalAtlas he).comp
      ((contMDiffOn_symm_of_mem_maximalAtlas hh).mono (fun z hz => hz.1))
      (fun z hz => hz.2)).contDiffOn
  exact contDiffOn_fst.prodMk (ht.comp contDiffOn_snd (fun z hz => hz.2))

theorem passiveRaw_observer_argument_jets
    (e host : OpenPartialHomeomorph M D)
    (he : e ∈ maximalAtlas IM ∞ M) (hh : host ∈ maximalAtlas IM ∞ M)
    (R : Set X) (hR : IsCompact R)
    (hRO : R ⊆ passiveOriginalObserverDomain (OpenPartialHomeomorph.refl Ep) e host) :
    ∃ T : ℕ → ℝ, (∀ k, 0 ≤ T k) ∧
    ∀ (n length j Rsub Lprimary : ℕ) (reserve Bnd Mg : ℝ) (Tbackground : ℕ → ℝ)
      (F : Ep → M → V) (hF : ∀ p, ContMDiff IM 𝓘(ℝ,V) ∞ (F p))
      (g : IncrementsGlobalPrimaryFamily (I := IM) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
      (input inputbar : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
      (W : Set (Ep × M)) (primary : Λ → Set (Ep × M))
      (O S : Set X) (tau ell Delta : ℝ)
      (data : ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n length j Rsub Lprimary
        reserve Bnd Mg Tbackground F hF g input inputbar W primary e O S tau ell Delta),
      MapsTo (passiveRawObserverTransition e host) R S →
      ∀ nu k, k ≤ j+1 → ∀ z ∈ R,
        (z.1,host.symm z.2) ∈ incrementsGlobalRelativeSupport W (g.cutoff nu) →
        ell^k*‖iteratedFDeriv ℝ k (fun w : X =>
          g.linearArgument nu w.1 (host.symm w.2) (input w.1 (host.symm w.2))) z‖ ≤
          actualFastChartTransferPrefix T (j+1) * (2^(j+1)*Bnd^2) := by
  let phi := passiveRawObserverTransition (d := d) e host
  let Overlap := passiveOriginalObserverDomain (OpenPartialHomeomorph.refl Ep) e host
  have hOverlap : IsOpen Overlap := passiveOriginalObserverDomain_open _ _ _
  have hphi : ContDiffOn ℝ ∞ phi Overlap := passiveRawObserverTransition_smooth e host he hh
  obtain ⟨T,hT,hTbound⟩ := round3_prepared_compact_profiles phi Overlap R hOverlap hR hRO hphi
  refine ⟨T,hT,?_⟩
  intro n length j Rsub Lprimary reserve Bnd Mg Tbackground F hF g input inputbar W primary
    O S tau ell Delta data hSample nu k hk z hz hActive
  have hell : 0 < ell := data.htau.trans_le data.htaul
  have hpoint (w : X) (hw : w ∈ Overlap) :
      ((phi w).1,e.symm (phi w).2) = (w.1,host.symm w.2) := by
    change (w.1,e.symm (e (host.symm w.2))) = _
    exact Prod.ext rfl (e.left_inv hw.2.2)
  have hOldActive : (phi z).1 ∈ (univ : Set Ep) ∧
      ((phi z).1,e.symm (phi z).2) ∈ incrementsGlobalRelativeSupport W (g.cutoff nu) := by
    rw [hpoint z (hRO hz)]
    exact ⟨mem_univ _,hActive⟩
  have hzOld : phi z ∈ S ∩ (fun w : X => (w.1,e.symm w.2)) ⁻¹'
      incrementsGlobalRelativeSupport W (g.cutoff nu) := ⟨hSample hz,hOldActive.2⟩
  let U := Overlap ∩ phi ⁻¹' data.Omega nu
  have hU : IsOpen U := hphi.continuousOn.isOpen_inter_preimage hOverlap (data.hOmega nu)
  have hzU : z ∈ U := ⟨hRO hz,data.hSOmega nu hzOld⟩
  let f := fun w : X => data.Lobs nu w (data.Aobs nu w)
  have hf : ContDiffOn ℝ ∞ f (data.Omega nu) := (data.hLobs nu).clm_apply (data.hAobs nu)
  have hfb : ∀ r ≤ k, ell^r*‖iteratedFDeriv ℝ r f (phi z)‖ ≤ 2^(j+1)*Bnd^2 := by
    intro r hr
    have h := scaled_clm_apply (data.Omega nu) (data.hOmega nu) (data.Lobs nu) (data.Aobs nu)
      (data.hLobs nu) (data.hAobs nu) r 0 ell Bnd Bnd hell.le
      (fun s hs => data.hLobsb nu s (hs.trans (hr.trans hk)) (phi z) hzOld)
      (fun a ha => by simpa only [Nat.add_zero] using (data.hAobsb nu a (ha.trans (hr.trans hk)) (phi z) hzOld))
      (data.hSOmega nu hzOld)
    simp only [Nat.add_zero] at h
    apply h.trans
    calc
      2^r*Bnd*Bnd = 2^r*Bnd^2 := by ring
      _ ≤ 2^(j+1)*Bnd^2 := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (hr.trans hk)) (sq_nonneg _)
  have htrans := actual_fast_joint_chart_transfer T hT k phi f U (data.Omega nu)
    hU (data.hOmega nu) (hphi.mono inter_subset_left) hf (fun w hw => hw.2) z hzU
    ell ell (2^(j+1)*Bnd^2) hell le_rfl hfb
    (fun a _ _ => (hTbound ell hell.le data.hell1 a z hz).2)
  let arg := fun w : X => g.linearArgument nu w.1 (host.symm w.2) (input w.1 (host.symm w.2))
  have heq : EqOn arg (f ∘ phi) U := by
    intro w hw
    dsimp only [Function.comp_apply,f]
    rw [data.hRepobs nu (phi w) hw.2]
    change g.linearArgument nu w.1 (host.symm w.2) (input w.1 (host.symm w.2)) =
      g.linearArgument nu w.1 (e.symm (e (host.symm w.2)))
        (input w.1 (e.symm (e (host.symm w.2))))
    have hx : e.symm (e (host.symm w.2)) = host.symm w.2 :=
      congrArg Prod.snd (hpoint w hw.1)
    rw [hx]
  have he : arg =ᶠ[nhds z] f ∘ phi := heq.eventuallyEq_of_mem (hU.mem_nhds hzU)
  change ell^k*‖iteratedFDeriv ℝ k arg z‖ ≤ _
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
  exact htrans.trans (mul_le_mul_of_nonneg_right
    (actualFastChartTransferCost_le_prefix T hT hk) (by positivity))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.passiveRaw_observer_argument_jets
