import Smoothing.ParameterRound2ObserverLeadingIndex

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

theorem incrementCanonical_parameterRound2_actual_observer_leading_bounds_uniform_index
    (n : ℕ) (r : Fin (m+1)) (coord : Fin N) (c Bnd : ℝ) (hc : 0 < c) (hBnd : 0 ≤ Bnd) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Type uCanonicalM) [TopologicalSpace M] [ChartedSpace H M]
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
    (hPhi : ContDiffOn ℝ ∞ (fun z : X => g.phase ν (z.1,e.symm z.2)) O)
    (ell Delta : ℝ) (hell : 0 < ell) (hDelta : 0 ≤ Delta)
    (hReserve : ∀ z ∈ S, c ≤ L z (A z) ∧ c ≤ L z (Abar z))
    (hLb : ∀ r ≤ n, ∀ z ∈ S, ell^r*‖iteratedFDeriv ℝ r L z‖ ≤ Bnd)
    (hAb : ∀ r ≤ n, ∀ z ∈ S, ell^r*‖iteratedFDeriv ℝ r A z‖ ≤ Bnd)
    (hAbarb : ∀ r ≤ n, ∀ z ∈ S, ell^r*‖iteratedFDeriv ℝ r Abar z‖ ≤ Bnd)
    (hCutb : ∀ r ≤ n, ∀ z ∈ S, ell^r*‖iteratedFDeriv ℝ r (fun w : X => g.cutoff ν (w.1,e.symm w.2)) z‖ ≤ Bnd)
    (hNormalb : ∀ r ≤ n, ∀ z ∈ S, ell^r*‖iteratedFDeriv ℝ r (fun w : X => g.normal ν (w.1,e.symm w.2)) z‖ ≤ Bnd)
    (hPhib : ∀ k ≤ n, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k
      (fun w : X => fderiv ℝ (fun x => g.phase ν (w.1,e.symm x)) w.2 (EuclideanSpace.single r 1)) z‖ ≤ Bnd)
    (hDiff : ∀ r ≤ n, ∀ z ∈ S, ell^r*‖iteratedFDeriv ℝ r (fun w => A w-Abar w) z‖ ≤ Delta),
    let positive := O ∩ {z | 0 < L z (A z)} ∩ {z | 0 < L z (Abar z)}
    let leadA := fun z : X => incrementsGlobalObservedLeading F g input e z.1 z.2 ν r coord
    let leadB := fun z : X => incrementsGlobalObservedLeading F g inputbar e z.1 z.2 ν r coord
    (ContDiffOn ℝ ∞ leadA positive ∧ ContDiffOn ℝ ∞ leadB positive) ∧
    (∀ k ≤ n, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k leadA z‖ ≤ C) ∧
    (∀ k ≤ n, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k leadB z‖ ≤ C) ∧
    (∀ k ≤ n, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k (fun w => leadA w-leadB w) z‖ ≤ C*Delta) := by
  obtain ⟨C,hC,hbound⟩ := actual_joint_normalized_primary_leading_bounds_uniform
    (Ep := Ep) coord (EuclideanSpace.single r 1) n c Bnd hc hBnd
  refine ⟨C,hC,?_⟩
  intro M _ _ _ _
  intro Λ Β _ _ F g input inputbar ν e O S hO hSO L A Abar hL hA hAbar hRep hRepbar hCut hNormal hPhi
    ell Delta hell hDelta hReserve hLb hAb hAbarb hCutb hNormalb hPhib hDiff positive leadA leadB
  have hh := hbound O S hO hSO L A Abar
    (fun z : X => g.cutoff ν (z.1,e.symm z.2))
    (fun z : X => g.phase ν (z.1,e.symm z.2))
    (fun z : X => g.normal ν (z.1,e.symm z.2))
    hL hA hAbar hCut hPhi hNormal ell Delta hell hDelta hReserve
    hLb hAb hAbarb hCutb hNormalb hPhib hDiff
  let rawA := fun z : X => incrementsLeadingCoefficient 1
    (g.cutoff ν (z.1,e.symm z.2)*Real.sqrt (L z (A z))) (g.normal ν (z.1,e.symm z.2))
    (fun _ : Unit => fderiv ℝ (fun x => g.phase ν (z.1,e.symm x)) z.2 (EuclideanSpace.single r 1)) () coord
  let rawB := fun z : X => incrementsLeadingCoefficient 1
    (g.cutoff ν (z.1,e.symm z.2)*Real.sqrt (L z (Abar z))) (g.normal ν (z.1,e.symm z.2))
    (fun _ : Unit => fderiv ℝ (fun x => g.phase ν (z.1,e.symm x)) z.2 (EuclideanSpace.single r 1)) () coord
  have heA : EqOn leadA rawA O := by
    intro z hz
    simp only [leadA,rawA,incrementsGlobalObservedLeading,incrementsGlobalPrimaryB,
      incrementsLeadingCoefficient,hRep z hz]
  have heB : EqOn leadB rawB O := by
    intro z hz
    simp only [leadB,rawB,incrementsGlobalObservedLeading,incrementsGlobalPrimaryB,
      incrementsLeadingCoefficient,hRepbar z hz]
  have germA (z) (hz : z ∈ S) : leadA =ᶠ[𝓝 z] rawA :=
    eventuallyEq_of_mem (hO.mem_nhds (hSO hz)) (fun w hw => heA hw)
  have germB (z) (hz : z ∈ S) : leadB =ᶠ[𝓝 z] rawB :=
    eventuallyEq_of_mem (hO.mem_nhds (hSO hz)) (fun w hw => heB hw)
  refine ⟨⟨hh.1.1.congr (fun z hz => heA hz.1.1),hh.1.2.congr (fun z hz => heB hz.1.1)⟩,?_,?_,?_⟩
  · intro k hk z hz
    rw [((germA z hz).iteratedFDeriv ℝ k).eq_of_nhds]
    exact hh.2.1 k hk z hz
  · intro k hk z hz
    rw [((germB z hz).iteratedFDeriv ℝ k).eq_of_nhds]
    exact hh.2.2.1 k hk z hz
  · intro k hk z hz
    change ell^k*‖iteratedFDeriv ℝ k (leadA-leadB) z‖ ≤ C*Delta
    rw [(((germA z hz).sub (germB z hz)).iteratedFDeriv ℝ k).eq_of_nhds]
    exact hh.2.2.2 k hk z hz

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.incrementCanonical_parameterRound2_actual_observer_leading_bounds_uniform_index
