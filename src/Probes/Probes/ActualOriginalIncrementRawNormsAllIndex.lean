import Probes.ActualOriginalIncrementRawJetsAllIndex
import Probes.ActualOriginalIncrementNormShift
import Smoothing.ParameterRound2MeanRawNative
import Probes.ActualIncrementOriginalCoordinateJets

/-! Raw original profiles, the fixed actual secondary choices and the true
inverse parameter charts produce the SAME literal displacement in
the unchanged original weighted atlas norm. The constant precedes every
actual atlas, field, scale and cutoff choice. All observation charts see
one and the same global map. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set Manifold IsManifold
open scoped ContDiff Classical ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M Tr : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ
private local instance rawNormTensorSemi : SeminormedAddCommGroup Tensor := ContinuousLinearMap.toSeminormedAddCommGroup
private local instance rawNormTensorNormed : NormedAddCommGroup Tensor := ContinuousLinearMap.toNormedAddCommGroup
private local instance rawNormTensorSpace : NormedSpace ℝ Tensor := ContinuousLinearMap.toNormedSpace

 theorem actual_original_increment_raw_paper_norms_uniform_all_index
    (nInput nSolve j q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (hSolve : j+2+(q+2) ≤ nSolve) (hInput : nSolve+2+(q+2) ≤ nInput)
    (reserve Bnd Mg Kcut : ℝ) (hc : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (T Tinv Tobs TP : ℕ → ℝ)
    (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k) (hTP : ∀ k, 0 ≤ TP k) :
    ∃ CR : ℝ, 0 ≤ CR ∧ ∀ (Label SubPrimary SubSecondary : Type*)
      [Fintype Label] [DecidableEq Label] [Fintype SubPrimary] [Fintype SubSecondary], ∀ (pcount : ℕ), ∀
      (A : BufferedAtlas M D) (B : Fin pcount → OpenPartialHomeomorph Ep Ep)
      (_hA : IsSmoothBufferedAtlas A) (_hB : ∀ i, B i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ Ep)
      (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
      (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
      (input inputbar : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
      (W : Set (Ep × M)) (primary : Label → Set (Ep × M))
      (S : Fin A.count × Fin pcount → Set (Fin (m+1+d) → ℝ))
      (_hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
      (ell delta tau Delta : ℝ) (_htau : 0 < tau) (_htaul : tau ≤ ell) (_hell1 : ell ≤ 1)
      (_hdelta : 0 ≤ delta) (_hdeltatau : delta ≤ tau)
      (choice : ActualSecondarySignedRecord Label → SubSecondary → ActualOriginalSecondaryChoice Ep M m)
      (raw : ActualOriginalSecondaryRawData (Tr := Tr) F hF g input inputbar nInput nSolve j q Rsub Lprimary
        reserve Bnd Mg Kcut T Tinv W primary ell delta tau Delta choice)
      (Omega : Fin A.count × Fin pcount → Set X)
      (_obs : ∀ i : Fin A.count × Fin pcount, ActualOriginalSecondaryObservationData raw Tobs Rsecondary
        (A.chart i.1) (Omega i)
        (parameterRound2_meanParameterMap (m := m) (B i.2) '' ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i)))
      (_hParam : ∀ i : Fin A.count × Fin pcount, ∀ z : X,
        parameterTensorModelEquiv (m+1) d z ∈ S i → ∀ k, 1 ≤ k → k ≤ j+1 →
        ell^(k-1)*‖iteratedFDeriv ℝ k (parameterRound2_meanParameterMap (m := m) (B i.2)) z‖ ≤ TP k),
    let U := actualOriginalIncrementMap F hF g input (q+2) tau delta choice
    let coordinates := incrementsOriginalMapCoordinates A B U
    (∀ i, ∃ G : Set (Fin (m+1+d) → ℝ), IsOpen G ∧ S i ⊆ G ∧
      G ⊆ incrementsOriginalDifferentiation A B i ∧ ContDiffOn ℝ ∞ (coordinates i) G) ∧
    (paperAtlasWeighted 0 (j+1) tau coordinates (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
      (paperAtlasWeighted 0 (j+1) tau coordinates (incrementsOriginalDifferentiation A B) S).toReal ≤ CR*delta*tau) ∧
    (paperAtlasWeighted 1 j tau coordinates (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
      (paperAtlasWeighted 1 j tau coordinates (incrementsOriginalDifferentiation A B) S).toReal ≤ CR*delta) := by
  obtain ⟨K,hK,hraw⟩ := actual_original_increment_raw_jets_uniform_all_index
    (m := m) (N := N) («Ep» := Ep) (M := M) (Tr := Tr)
    nInput nSolve j q Rsub Lprimary Rsecondary hq hSolve hInput reserve Bnd Mg Kcut hc hBnd hMg hKcut
    T Tinv Tobs hT hTinv hTobs
  let a := parameterTensorModelEquiv (m+1) d
  let target := (EuclideanSpace.equiv (Fin N) ℝ).toContinuousLinearMap
  let CP := actualFastChartTransferPrefix TP (j+1)
  have hCP : 0 ≤ CP := actualFastChartTransferPrefix_nonneg TP hTP (j+1)
  let K0 := linearModelFactor a.symm (j+1)*‖target‖*(CP*K)
  have hK0 : 0 ≤ K0 := mul_nonneg
    (mul_nonneg (linearModelFactor_nonneg _ _) (norm_nonneg _)) (mul_nonneg hCP hK)
  refine ⟨(j+2)*K0,mul_nonneg (by positivity) hK0,?_⟩
  intro Label SubPrimary SubSecondary _ _ _ _ pcount A B _hA hB F hF g input inputbar W primary S hSO ell delta tau Delta htau htaul hell1
    hdelta hdeltatau choice raw Omega obs hParam U coordinates
  let phi := fun i : Fin A.count × Fin pcount => parameterRound2_meanParameterMap (m := m) (B i.2)
  let O := fun i : Fin A.count × Fin pcount => (B i.2).target ×ˢ (A.chart i.1).target
  let S0 := fun i => a ⁻¹' S i
  let S1 := fun i => phi i '' S0 i
  let U0 := fun i : Fin A.count × Fin pcount => fun z : X => U (z.1,(A.chart i.1).symm z.2)
  let UN := fun i => U0 i ∘ phi i
  have hO (i) : IsOpen (O i) := (B i.2).open_target.prod (A.chart i.1).open_target
  have hSO0 : ∀ i, S0 i ⊆ O i := by
    intro i z hz
    have hh := hSO i hz
    have he : (incrementsOriginalParameterPoint (a z),incrementsOriginalSourcePoint (a z)) = z := a.symm_apply_apply z
    rw [← he]
    exact ⟨hh.2,hh.1⟩
  have hphi (i) : ContDiffOn ℝ ∞ (phi i) (O i) :=
    (((contMDiffOn_symm_of_mem_maximalAtlas (hB i.2)).contDiffOn).comp
      contDiffOn_fst (fun _ hz => hz.1)).prodMk contDiffOn_snd
  let V0 := fun i => O i ∩ phi i ⁻¹' Omega i
  have hV (i) : IsOpen (V0 i) :=
    (hphi i).continuousOn.isOpen_inter_preimage (hO i) (obs i).profiles.hO
  have hSV : ∀ i, S0 i ⊆ V0 i := fun i z hz =>
    ⟨hSO0 i hz,(obs i).profiles.hSO ⟨z,hz,rfl⟩⟩
  have hh (i) := hraw Label SubPrimary SubSecondary F hF g input inputbar W primary ell delta tau Delta hdelta hdeltatau choice raw
    (A.chart i.1) (Omega i) (S1 i) (obs i)
  have hsm (i) : ContDiffOn ℝ ∞ (UN i) (V0 i) :=
    (hh i).1.comp ((hphi i).mono inter_subset_left) (fun _ hz => hz.2)
  have hjets : ∀ i, ∀ k ≤ j+1, ∀ z ∈ S0 i,
      tau^k*‖iteratedFDeriv ℝ k (UN i) z‖ ≤ (CP*K)*delta*tau := by
    intro i k hk z hz
    have ht := actual_fast_joint_chart_transfer TP hTP k (phi i) (U0 i) (V0 i) (Omega i)
      (hV i) (obs i).profiles.hO ((hphi i).mono inter_subset_left) (hh i).1
      (fun _ hy => hy.2) z (hSV i hz) tau ell (K*delta*tau) htau htaul
      (fun r hr => (hh i).2 r (hr.trans hk) (phi i z) ⟨z,hz,rfl⟩)
      (fun r hr hrk => hParam i z hz r hr (hrk.trans hk))
    exact (ht.trans (mul_le_mul_of_nonneg_right
      (actualFastChartTransferCost_le_prefix TP hTP hk) (by positivity))).trans_eq (by ring)
  let OC := modelCoordinateDomains a V0
  have hOC : ∀ i, IsOpen (OC i) := modelCoordinateDomains_open a hV
  have hSOC : ∀ i, S i ⊆ OC i := by
    intro i z hz
    apply hSV i
    change a (a.symm z) ∈ S i
    simpa using hz
  have hOCorig : ∀ i, OC i ⊆ incrementsOriginalDifferentiation A B i := by
    intro i y hy
    exact ⟨hy.1.2,hy.1.1⟩
  have hcoord (i) : coordinates i = target ∘ UN i ∘ a.symm := rfl
  have hcoords (i) : ContDiffOn ℝ ∞ (coordinates i) (OC i) := by
    rw [hcoord]
    exact target.contDiff.comp_contDiffOn
      ((hsm i).comp a.symm.contDiff.contDiffOn (fun _ hz => hz))
  have hcb : ∀ i, ∀ k ≤ j+1, ∀ y ∈ S i,
      tau^k*‖iteratedFDeriv ℝ k (coordinates i) y‖ ≤ K0*delta*tau := by
    intro i k hk y hy
    have hy' : a.symm y ∈ S0 i := by change a (a.symm y) ∈ S i; simpa using hy
    have hpre := norm_iteratedFDeriv_comp_equiv_le a.symm (UN i) k y
    have hbpre : tau^k*‖iteratedFDeriv ℝ k (UN i ∘ a.symm) y‖ ≤
        linearModelFactor a.symm (j+1)*((CP*K)*delta*tau) := by
      calc
        _ ≤ tau^k*(‖iteratedFDeriv ℝ k (UN i) (a.symm y)‖*linearModelFactor a.symm k) :=
          mul_le_mul_of_nonneg_left hpre (pow_nonneg htau.le k)
        _ = linearModelFactor a.symm k*(tau^k*‖iteratedFDeriv ℝ k (UN i) (a.symm y)‖) := by ring
        _ ≤ _ := mul_le_mul (linearModelFactor_mono a.symm hk) (hjets i k hk _ hy')
          (by positivity) (linearModelFactor_nonneg _ _)
    have hpost := slow_linear_jet_bound target (OC i) (hOC i) (UN i ∘ a.symm)
      ((hsm i).comp a.symm.contDiff.contDiffOn (fun _ hz => hz)) k tau
      (linearModelFactor a.symm (j+1)*((CP*K)*delta*tau)) htau.le y (hSOC i hy) hbpre
    rw [hcoord]
    exact hpost.trans_eq (by dsimp only [K0]; ring)
  have hn0 := parameterRound2_paperAtlasWeighted_le_of_weighted_jets (j+1) tau
    (K0*delta*tau) htau (htaul.trans hell1) (by positivity) coordinates OC S hOC hSOC hcoords hcb
  have hn1 := actual_paper_base_one_from_weighted_jets j tau
    (K0*delta*tau) htau (htaul.trans hell1) (by positivity) coordinates OC S hOC hSOC hcoords hcb
  have hrestrict (base r : ℕ) := actual_paperAtlasWeighted_open_restrict base r tau coordinates
    (incrementsOriginalDifferentiation A B) OC S (parameterRound2_originalDifferentiation_open A B)
    hOC hOCorig hSOC
  rw [← hrestrict 0 (j+1)] at hn0
  rw [← hrestrict 1 j] at hn1
  refine ⟨fun i => ⟨OC i,hOC i,hSOC i,hOCorig i,hcoords i⟩,⟨hn0.1,?_⟩,⟨hn1.1,?_⟩⟩
  · exact hn0.2.trans_eq (by push_cast; ring)
  · have hcancel : K0*delta*tau/tau = K0*delta := mul_div_cancel_right₀ _ htau.ne'
    rw [hcancel] at hn1
    have hj : (j+1 : ℝ) ≤ j+2 := by linarith
    exact hn1.2.trans ((mul_le_mul_of_nonneg_right hj (mul_nonneg hK0 hdelta)).trans_eq (by ring))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_increment_raw_paper_norms_uniform_all_index
