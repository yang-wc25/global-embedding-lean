import NormalPolar.PassiveRawObserverTransfer

/-! The raw primary-coordinate transitions in an additional host are
produced from the same old raw record. Both cutoff-active sets are moved by
the true physical-point identity; no extra transition estimate is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical BigOperators
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

theorem passiveRaw_observer_primary_chart_jets
    (e host : OpenPartialHomeomorph M D)
    (he : e ∈ maximalAtlas IM ∞ M) (hh : host ∈ maximalAtlas IM ∞ M)
    (R : Set X) (hR : IsCompact R)
    (hRO : R ⊆ passiveOriginalObserverDomain (OpenPartialHomeomorph.refl Ep) e host) :
    ∃ T : ℕ → ℝ, (∀ k, 0 ≤ T k) ∧
    ∀ (n length j Rsub Lprimary : ℕ) (reserve Bnd Mg : ℝ) (Tbackground : ℕ → ℝ),
      (∀ k, 0 ≤ Tbackground k) →
      ∀ (F : Ep → M → V) (hF : ∀ p, ContMDiff IM 𝓘(ℝ,V) ∞ (F p))
      (g : IncrementsGlobalPrimaryFamily (I := IM) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
      (input inputbar : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
      (W : Set (Ep × M)) (primary : Λ → Set (Ep × M))
      (O S : Set X) (tau ell Delta : ℝ)
      (data : ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n length j Rsub Lprimary
        reserve Bnd Mg Tbackground F hF g input inputbar W primary e O S tau ell Delta),
      MapsTo (passiveRawObserverTransition e host) R S →
      ∀ nu beta k, 1 ≤ k → k ≤ j+1 → ∀ z ∈ R,
        (z.1,host.symm z.2) ∈ incrementsGlobalRelativeSupport W (g.cutoff nu) →
        (z.1,host.symm z.2) ∈ incrementsGlobalRelativeSupport W
          (fun w => g.eta nu beta w*g.cutoff nu w) →
        ell^(k-1)*‖iteratedFDeriv ℝ k
          (fun w : X => g.chart nu beta (w.1,host.symm w.2)) z‖ ≤
            actualFastChartTransferPrefix T k*bufferedTransitionPrefix Tbackground k := by
  obtain ⟨T,hT,hTransfer⟩ := passiveRaw_observer_positive_field_transfer (Y := X) e host he hh R hR hRO
  refine ⟨T,hT,?_⟩
  intro n length j Rsub Lprimary reserve Bnd Mg Tbackground hTb F hF g input inputbar W primary
    O S tau ell Delta data hSample nu beta k hk1 hk z hz hCut hEta
  let phi := passiveRawObserverTransition (d := d) e host
  let Sold := (S ∩ (fun w : X => (w.1,e.symm w.2)) ⁻¹'
    incrementsGlobalRelativeSupport W (g.cutoff nu)) ∩
      (fun w : X => (w.1,e.symm w.2)) ⁻¹'
        incrementsGlobalRelativeSupport W (fun w => g.eta nu beta w*g.cutoff nu w)
  have hSO : Sold ⊆ data.U nu beta := fun w hw =>
    data.hOU nu beta ⟨data.hSOmega nu hw.1,hw.2⟩
  have hpoint := passiveRawObserverTransition_point e host z (hRO hz)
  have hzS : phi z ∈ Sold := by
    refine ⟨⟨hSample hz,?_⟩,?_⟩
    · change ((phi z).1,e.symm (phi z).2) ∈ incrementsGlobalRelativeSupport W (g.cutoff nu)
      rw [hpoint]
      exact hCut
    · change ((phi z).1,e.symm (phi z).2) ∈ incrementsGlobalRelativeSupport W
        (fun w => g.eta nu beta w*g.cutoff nu w)
      rw [hpoint]
      exact hEta
  have hprefix (a : ℕ) (ha : a ≤ k) : Tbackground a ≤ bufferedTransitionPrefix Tbackground k := by
    have hh := Finset.single_le_sum (fun l (_ : l ∈ Finset.range (k+1)) => hTb l)
      (show a ∈ Finset.range (k+1) by simp; omega)
    exact hh.trans (by unfold bufferedTransitionPrefix; linarith)
  exact hTransfer (g.chart nu beta) (data.U nu beta) Sold (data.hU nu beta) hSO
    (data.hphi nu beta) k ell (bufferedTransitionPrefix Tbackground k)
    (data.htau.trans_le data.htaul) data.hell1
    (zero_le_one.trans (one_le_bufferedTransitionPrefix hTb k))
    (fun a ha hak w hw => (data.hphib nu beta a ha (hak.trans hk) w hw).trans (hprefix a hak))
    k hk1 le_rfl z hz hzS

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.passiveRaw_observer_primary_chart_jets
