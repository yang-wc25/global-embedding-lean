import Smoothing.ParameterRound2ObserverFreeIndex

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
universe uCanonicalM
variable {E H Ep Tr : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

theorem incrementCanonical_parameterRound2_actual_observer_free_bounds_uniform_index
    (n : ℕ) (c Bnd : ℝ) (hc : 0 < c) (hBnd : 0 ≤ Bnd) :
    ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ (M : Type uCanonicalM) [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [BoundarylessManifold I M], ∀ {Λ Β : Type*} [Fintype Λ] [Fintype Β]
    (F : Ep → M → V)
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input inputbar : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (ν : Λ) (e : OpenPartialHomeomorph M D) (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O)
    (L : X → Tr →L[ℝ] ℝ) (A Abar : X → Tr)
    (hL : ContDiffOn ℝ ∞ L O) (hA : ContDiffOn ℝ ∞ A O) (hAbar : ContDiffOn ℝ ∞ Abar O)
    (hRep : ∀ z ∈ O, L z (A z) = g.linearArgument ν z.1 (e.symm z.2) (input z.1 (e.symm z.2)))
    (hRepbar : ∀ z ∈ O, L z (Abar z) = g.linearArgument ν z.1 (e.symm z.2) (inputbar z.1 (e.symm z.2)))
    (hCut : ContDiffOn ℝ ∞ (fun z : X => g.cutoff ν (z.1,e.symm z.2)) O)
    (hNormal : ContDiffOn ℝ ∞ (fun z : X => g.normal ν (z.1,e.symm z.2)) O)
    (ell tau Delta : ℝ) (hell : 0 < ell) (htau : 0 ≤ tau) (hDelta : 0 ≤ Delta)
    (hReserve : ∀ z ∈ S, c ≤ L z (A z) ∧ c ≤ L z (Abar z))
    (hLb : ∀ r ≤ n, ∀ z ∈ S, ell^r*‖iteratedFDeriv ℝ r L z‖ ≤ Bnd)
    (hAb : ∀ r ≤ n, ∀ z ∈ S, ell^r*‖iteratedFDeriv ℝ r A z‖ ≤ Bnd)
    (hAbarb : ∀ r ≤ n, ∀ z ∈ S, ell^r*‖iteratedFDeriv ℝ r Abar z‖ ≤ Bnd)
    (hCutb : ∀ r ≤ n, ∀ z ∈ S, ell^r*‖iteratedFDeriv ℝ r (fun w : X => g.cutoff ν (w.1,e.symm w.2)) z‖ ≤ Bnd)
    (hNormalb : ∀ r ≤ n, ∀ z ∈ S, ell^r*‖iteratedFDeriv ℝ r (fun w : X => g.normal ν (w.1,e.symm w.2)) z‖ ≤ Bnd)
    (hDiff : ∀ r ≤ n, ∀ z ∈ S, ell^r*‖iteratedFDeriv ℝ r (fun w => A w-Abar w) z‖ ≤ Delta),
    let positive := O ∩ {z | 0 < L z (A z)} ∩ {z | 0 < L z (Abar z)}
    let bA := fun z : X => incrementsGlobalPrimaryB F g input ν (z.1,e.symm z.2)
    let bB := fun z : X => incrementsGlobalPrimaryB F g inputbar ν (z.1,e.symm z.2)
    let freeA := fun z : X => incrementsGlobalPrimaryFree F g input tau ν (z.1,e.symm z.2)
    let freeB := fun z : X => incrementsGlobalPrimaryFree F g inputbar tau ν (z.1,e.symm z.2)
    (ContDiffOn ℝ ∞ bA positive ∧ ContDiffOn ℝ ∞ bB positive) ∧
    (ContDiffOn ℝ ∞ freeA positive ∧ ContDiffOn ℝ ∞ freeB positive) ∧
    (∀ r ≤ n, ∀ z ∈ S, ell^r*‖iteratedFDeriv ℝ r freeA z‖ ≤ Cv*tau) ∧
    (∀ r ≤ n, ∀ z ∈ S, ell^r*‖iteratedFDeriv ℝ r freeB z‖ ≤ Cv*tau) ∧
    (∀ r ≤ n, ∀ z ∈ S, ell^r*‖iteratedFDeriv ℝ r (fun w => freeA w-freeB w) z‖ ≤ Cv*tau*Delta) := by
  obtain ⟨Ca,hCa,hsize⟩ := increments_positive_reserve_amplitude_scaled_jets n c Bnd hc hBnd
  obtain ⟨Cd,hCd,hdiff⟩ := increments_positive_reserve_amplitude_difference_scaled_jets n c Bnd hc hBnd
  let C := max Ca Cd
  have hC : 0 ≤ C := hCa.trans (le_max_left _ _)
  refine ⟨|Real.sqrt 2| *C,mul_nonneg (abs_nonneg _) hC,?_⟩
  intro M _ _ _ _
  intro Λ Β _ _ F g input inputbar ν e O S hO hSO L A Abar hL hA hAbar hRep hRepbar hCut hNormal
    ell tau Delta hell htau hDelta hReserve hLb hAb hAbarb hCutb hNormalb hDiff positive bA bB freeA freeB
  let cut := fun z : X => g.cutoff ν (z.1,e.symm z.2)
  let normal := fun z : X => g.normal ν (z.1,e.symm z.2)
  let vA := fun z => (cut z*Real.sqrt (L z (A z))) • normal z
  let vB := fun z => (cut z*Real.sqrt (L z (Abar z))) • normal z
  have hPosO : positive ⊆ O := fun z hz => hz.1.1
  have hvA := hsize O S hO hSO L A cut normal hL hA hCut hNormal ell hell
    (fun z hz => (hReserve z hz).1) hLb hAb hCutb hNormalb
  have hvB := hsize O S hO hSO L Abar cut normal hL hAbar hCut hNormal ell hell
    (fun z hz => (hReserve z hz).2) hLb hAbarb hCutb hNormalb
  have hvD := hdiff O S hO hSO L A Abar cut normal hL hA hAbar hCut hNormal
    ell Delta hell hDelta hReserve hLb hAb hAbarb hCutb hNormalb hDiff
  have hsA : ContDiffOn ℝ ∞ (fun z => Real.sqrt (L z (A z))) positive :=
    ((hL.clm_apply hA).mono hPosO).sqrt (fun z hz => hz.1.2.ne')
  have hsB : ContDiffOn ℝ ∞ (fun z => Real.sqrt (L z (Abar z))) positive :=
    ((hL.clm_apply hAbar).mono hPosO).sqrt (fun z hz => hz.2.ne')
  have hbA : ContDiffOn ℝ ∞ bA positive := by
    apply ((hCut.mono hPosO).mul hsA).congr
    intro z hz
    simp only [bA,incrementsGlobalPrimaryB,← hRep z hz.1.1]
  have hbB : ContDiffOn ℝ ∞ bB positive := by
    apply ((hCut.mono hPosO).mul hsB).congr
    intro z hz
    simp only [bB,incrementsGlobalPrimaryB,← hRepbar z hz.1.1]
  have hfreeA : ContDiffOn ℝ ∞ freeA positive :=
    (hbA.const_smul (Real.sqrt 2*tau)).smul (hNormal.mono hPosO)
  have hfreeB : ContDiffOn ℝ ∞ freeB positive :=
    (hbB.const_smul (Real.sqrt 2*tau)).smul (hNormal.mono hPosO)
  have hEqA : EqOn freeA (fun z => (Real.sqrt 2*tau) • vA z) O := by
    intro z hz
    simp only [freeA,vA,cut,normal,incrementsGlobalPrimaryFree,incrementsGlobalPrimaryB,hRep z hz,smul_smul]
  have hEqB : EqOn freeB (fun z => (Real.sqrt 2*tau) • vB z) O := by
    intro z hz
    simp only [freeB,vB,cut,normal,incrementsGlobalPrimaryFree,incrementsGlobalPrimaryB,hRepbar z hz,smul_smul]
  have hscaled (f v : X → V) (R : ℝ) (heq : EqOn f (fun z => (Real.sqrt 2*tau) • v z) O)
      (r : ℕ) (z : X) (hz : z ∈ S) (hv : ContDiffAt ℝ ∞ v z)
      (hb : ell^r*‖iteratedFDeriv ℝ r v z‖ ≤ R) :
      ell^r*‖iteratedFDeriv ℝ r f z‖ ≤ |Real.sqrt 2| *tau*R := by
    have he : f =ᶠ[𝓝 z] (fun z => (Real.sqrt 2*tau) • v z) :=
      eventuallyEq_of_mem (hO.mem_nhds (hSO hz)) (fun w hw => heq hw)
    rw [(he.iteratedFDeriv ℝ r).eq_of_nhds,
      iteratedFDeriv_const_smul_apply' (hv.of_le (by simp : (r : ℕ∞ω) ≤ ∞)),
      norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg htau]
    calc
      _ = (|Real.sqrt 2| *tau)*(ell^r*‖iteratedFDeriv ℝ r v z‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (by positivity)
  have hVA (z : X) (hz : z ∈ S) : ContDiffAt ℝ ∞ vA z :=
    increments_positive_reserve_amplitude_contDiffAt O hO L A cut normal hL hA hCut hNormal
      (hSO hz) (hc.trans_le (hReserve z hz).1)
  have hVB (z : X) (hz : z ∈ S) : ContDiffAt ℝ ∞ vB z :=
    increments_positive_reserve_amplitude_contDiffAt O hO L Abar cut normal hL hAbar hCut hNormal
      (hSO hz) (hc.trans_le (hReserve z hz).2)
  refine ⟨⟨hbA,hbB⟩,⟨hfreeA,hfreeB⟩,?_,?_,?_⟩
  · intro r hr z hz
    calc
      _ ≤ |Real.sqrt 2| *tau*Ca := hscaled freeA vA Ca hEqA r z hz (hVA z hz) (hvA r hr z hz)
      _ ≤ |Real.sqrt 2| *tau*C := mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
      _ = _ := by ring
  · intro r hr z hz
    calc
      _ ≤ |Real.sqrt 2| *tau*Ca := hscaled freeB vB Ca hEqB r z hz (hVB z hz) (hvB r hr z hz)
      _ ≤ |Real.sqrt 2| *tau*C := mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
      _ = _ := by ring
  · intro r hr z hz
    have heq : EqOn (fun w => freeA w-freeB w) (fun w => (Real.sqrt 2*tau) • (vA w-vB w)) O := by
      intro w hw
      change freeA w-freeB w = (Real.sqrt 2*tau) • (vA w-vB w)
      rw [hEqA hw,hEqB hw,smul_sub]
    calc
      _ ≤ |Real.sqrt 2| *tau*(Cd*Delta) := hscaled _ _ _ heq r z hz ((hVA z hz).sub (hVB z hz)) (hvD r hr z hz)
      _ ≤ |Real.sqrt 2| *tau*(C*Delta) := by gcongr; exact le_max_right _ _
      _ = _ := by ring

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.incrementCanonical_parameterRound2_actual_observer_free_bounds_uniform_index
