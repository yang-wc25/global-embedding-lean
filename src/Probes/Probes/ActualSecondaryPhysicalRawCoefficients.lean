import Probes.ActualSecondaryRawCoefficients

/-! Original raw profiles produce the actual primary coefficient globally on
the observation domain. Active labels use their genuine positive open set;
inactive labels use the actual zero germ. No phase is differentiated outside
its original primary domain, and no coefficient/source/error output bound is
an input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {E H M Ep Tr : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

 theorem actual_original_physical_coefficient_profiles_from_raw
    (n q j Rsub Lprimary : ℕ) (hq : 1 ≤ q) (horder : j+2+(q+2) ≤ n)
    (c Bnd Mg : ℝ) (hc : 0 < c) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) :
    ∃ MD : ℝ, 0 ≤ MD ∧ ∀
      (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
      (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
      (input inputbar : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
      (W : Set (Ep × M)) (primary : Λ → Set (Ep × M))
      (e : OpenPartialHomeomorph M D)
      (he : ContMDiffOn I 𝓘(ℝ,D) ∞ e e.source)
      (heInv : ContMDiffOn 𝓘(ℝ,D) I ∞ e.symm e.target)
      (O S : Set X) (tau ell Delta : ℝ)
      (data : ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n (q+2) j Rsub Lprimary c Bnd Mg T
        F hF g input inputbar W primary e O S tau ell Delta)
      (hTarget : ∀ z ∈ O, z.2 ∈ e.target) (delta : ℝ) (nu : Λ),
    let phi := fun mu t x => g.phase mu (t,e.symm x)
    let P := fun mu t beta x => delta •
      incrementsGlobalPrimaryExtension F hF g input (q+2) tau true mu beta (t,e.symm x)
    let Q := fun mu t beta x => delta •
      incrementsGlobalPrimaryExtension F hF g input (q+2) tau false mu beta (t,e.symm x)
    let coeff := fun z : X => incrementsSecondaryPhysicalCoefficient phi tau (fun _ _ _ _ => 1)
      P Q (fun i _ => EuclideanSpace.single i 1) z nu
    ContDiffOn ℝ ∞ coeff O ∧
      (∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k coeff z‖ ≤ MD*|delta|) ∧
      (∀ z ∈ O, (z.1,e.symm z.2) ∉ incrementsGlobalRelativeSupport W (g.cutoff nu) →
        coeff =ᶠ[𝓝 z] 0) := by
  obtain ⟨MD,hMD,hraw⟩ := actual_original_observed_coefficient_profiles_from_raw
    (I := I) (M := M) (Ep := Ep) (Tr := Tr) (m := m) (N := N) (Λ := Λ) (Β := Β)
    n q j Rsub Lprimary hq horder c Bnd Mg hc hBnd hMg T hT
  refine ⟨MD,hMD,?_⟩
  intro F hF g input inputbar W primary e he heInv O S tau ell Delta data hTarget delta nu phi P Q coeff
  obtain ⟨hs,hb,hz⟩ := hraw F hF g input inputbar W primary e he heInv O S tau ell Delta data hTarget nu
  let nativeCoeff := fun z : X => incrementsGlobalObservedCoefficient F hF g input (q+2) tau e z.1 z.2 nu
  have heq : coeff = fun z => delta • nativeCoeff z := by
    funext z
    exact actual_original_primary_physical_coefficient_binding F hF g input (q+2) tau delta e z nu
  rw [heq]
  refine ⟨hs.const_smul delta,?_,?_⟩
  · intro k hk z hzS
    rw [iteratedFDeriv_const_smul_apply' ((hs.contDiffAt (data.hO.mem_nhds (data.hSO hzS))).of_le (by simp)),
      norm_smul,Real.norm_eq_abs]
    calc
      _ = |delta| *(ell^k*‖iteratedFDeriv ℝ k nativeCoeff z‖) := by ring
      _ ≤ |delta| *MD := mul_le_mul_of_nonneg_left (hb k hk z hzS) (abs_nonneg delta)
      _ = _ := mul_comm _ _
  · intro z hzO hn
    filter_upwards [hz z hzO hn] with w hw
    simp only [Pi.zero_apply] at hw
    change delta • incrementsGlobalObservedCoefficient F hF g input (q+2) tau e w.1 w.2 nu = 0
    rw [hw,smul_zero]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_physical_coefficient_profiles_from_raw
