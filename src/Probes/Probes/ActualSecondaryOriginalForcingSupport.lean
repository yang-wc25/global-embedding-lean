import Probes.ActualSecondaryOriginalConstruction
import Smoothing.ParameterRound2GlobalMeanSupport

/-! Original primary cutoff support forces the actual physical coefficient to
vanish. Consequently each genuine signed quadratic forcing is supported on
its original pair of primary cutoffs. No phase smoothness on an inactive
label and no requested coefficient or forcing budget is an assumption. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology BigOperators Classical ComplexConjugate
namespace GlobalEmbedding.Continuation
variable {m N : ℕ} {Ep M Label SubPrimary : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Label] [DecidableEq Label] [Fintype SubPrimary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ

 theorem actual_original_observed_coefficient_inactive
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (input : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (W : Set (Ep × M)) (primary : Label → Set (Ep × M))
    (h : ParameterRound2GlobalMeanPrimitives F hF g input W primary)
    (q : ℕ) (hq : 1 ≤ q) (tau : ℝ) (htau : 0 < tau)
    (e : OpenPartialHomeomorph M D)
    (he : ContMDiffOn 𝓙 𝓘(ℝ,D) ∞ e e.source)
    (heInv : ContMDiffOn 𝓘(ℝ,D) 𝓙 ∞ e.symm e.target)
    (z : X) (hz : z.2 ∈ e.target) (hzW : (z.1,e.symm z.2) ∈ W)
    (nu : Label) (hinactive : (z.1,e.symm z.2) ∉ incrementsGlobalRelativeSupport W (g.cutoff nu)) :
    incrementsGlobalObservedCoefficient F hF g input (q+2) tau e z.1 z.2 nu = 0 := by
  let b := (OpenPartialHomeomorph.refl Ep).prod e
  let O := b.target ∩ b.symm ⁻¹' W
  have hO : IsOpen O := b.symm.continuousOn.isOpen_inter_preimage b.open_target h.hW
  have hzO : z ∈ O := ⟨⟨Set.mem_univ _,hz⟩,hzW⟩
  have hh := parameterRound2_actual_globalObserved_inactive_germ F hF g input (q+2) tau W h.hW nu
    (h.hCombinedSupport nu) (h.hInverse nu) e O hO
    (b.symm.continuousOn.mono inter_subset_left) (fun y hy => hy.2) z hzO hinactive
  have hb := increments_global_primary_mean_binding F hF g input q hq tau htau W h.hW primary
    h.hPrimary h.hPrimarySupport h.hSourceW h.hChart h.hChartInv h.hInverse h.hCombinedSupport
    h.hPhase h.hCut h.hNormal h.hArgument h.hEta h.hPositive h.hUnit h.hPartition h.hSymm h.hDecomp
    h.hDouble h.hInteraction h.hG h.hJ h.hT0 h.hA h.hB h.hSecond
  have heq := congrFun (hb.2.2 e he heInv z.1 z.2 hz hzW).1 nu
  change incrementsGlobalObservedCoefficient F hF g input (q+2) tau e z.1 z.2 nu =
    incrementsGlobalObservedLeading F g input e z.1 z.2 nu+
      incrementsGlobalObservedError F hF g input (q+2) tau e z.1 z.2 nu at heq
  rw [heq,hh.1.eq_of_nhds,hh.2.eq_of_nhds]
  simp only [Pi.zero_apply,add_zero]

 theorem actual_secondary_quadratic_zero_of_coefficient
    (phi : Label → Ep → D → ℝ) (tau : ℝ)
    (chi : Label → Ep → SubPrimary → D → ℝ)
    (P Q : Label → Ep → SubPrimary → D → V)
    (z : X) (nu mu : Label) (branch : Fin 4)
    (hzero : incrementsSecondaryPhysicalCoefficient phi tau chi P Q
      (fun i _ => EuclideanSpace.single i 1) z nu = 0 ∨
      incrementsSecondaryPhysicalCoefficient phi tau chi P Q
      (fun i _ => EuclideanSpace.single i 1) z mu = 0) :
    incrementsSecondaryQuadraticForcing phi tau chi P Q
      (fun i _ => EuclideanSpace.single i 1) nu mu branch z = 0 := by
  rcases hzero with hzero | hzero
  · funext i j
    fin_cases branch <;> simp [incrementsSecondaryQuadraticForcing,hzero,dotProduct]
  · funext i j
    fin_cases branch <;> simp [incrementsSecondaryQuadraticForcing,hzero,dotProduct]

 theorem actual_original_quadratic_forcing_active_pair
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (input : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (W : Set (Ep × M)) (primary : Label → Set (Ep × M))
    (h : ParameterRound2GlobalMeanPrimitives F hF g input W primary)
    (q : ℕ) (hq : 1 ≤ q) (tau delta : ℝ) (htau : 0 < tau)
    (e : OpenPartialHomeomorph M D)
    (he : ContMDiffOn 𝓙 𝓘(ℝ,D) ∞ e e.source)
    (heInv : ContMDiffOn 𝓘(ℝ,D) 𝓙 ∞ e.symm e.target)
    (z : X) (hz : z.2 ∈ e.target) (hzW : (z.1,e.symm z.2) ∈ W)
    (r : (Label × Label) × Fin 4) :
    let H := actualOriginalSecondaryQuadratic F hF g input (q+2) tau delta e r z
    actualRealTensorAssembly H ≠ 0 ∨ actualImaginaryTensorAssembly H ≠ 0 →
      (z.1,e.symm z.2) ∈ incrementsGlobalRelativeSupport W (g.cutoff r.1.1) ∩
        incrementsGlobalRelativeSupport W (g.cutoff r.1.2) := by
  intro H hactive
  have hzCoeff (nu : Label) (hn : (z.1,e.symm z.2) ∉ incrementsGlobalRelativeSupport W (g.cutoff nu)) :
      incrementsSecondaryPhysicalCoefficient
        (fun l p x => g.phase l (p,e.symm x)) tau (fun _ _ _ _ => 1)
        (fun l p beta x => delta • incrementsGlobalPrimaryExtension F hF g input (q+2) tau true l beta (p,e.symm x))
        (fun l p beta x => delta • incrementsGlobalPrimaryExtension F hF g input (q+2) tau false l beta (p,e.symm x))
        (fun i _ => EuclideanSpace.single i 1) z nu = 0 := by
    rw [actual_original_primary_physical_coefficient_binding,
      actual_original_observed_coefficient_inactive F hF g input W primary h q hq tau htau e he heInv z hz hzW nu hn,
      smul_zero]
  have hzH (hn : (z.1,e.symm z.2) ∉ incrementsGlobalRelativeSupport W (g.cutoff r.1.1) ∨
      (z.1,e.symm z.2) ∉ incrementsGlobalRelativeSupport W (g.cutoff r.1.2)) : H = 0 := by
    apply actual_secondary_quadratic_zero_of_coefficient
    exact hn.elim (fun hn => Or.inl (hzCoeff _ hn)) (fun hn => Or.inr (hzCoeff _ hn))
  by_contra hn
  have hzero := hzH (not_and_or.mp hn)
  have hr : actualRealTensorAssembly H = 0 := by
    apply actual_bilinear_tensor_eq_of_basis
    intro i j
    rw [actualRealTensorAssembly_basis,hzero]
    simp
  have hi : actualImaginaryTensorAssembly H = 0 := by
    apply actual_bilinear_tensor_eq_of_basis
    intro i j
    rw [actualImaginaryTensorAssembly_basis,hzero]
    simp
  exact hactive.elim (fun hn => hn hr) (fun hn => hn hi)

 theorem actual_cutoff_inverse_support_on_target
    {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (b : OpenPartialHomeomorph Y Z) (rho : Y → ℝ) (K : Set Y)
    (hsupport : tsupport rho ⊆ K) (z : Z) (hz : z ∈ b.target)
    (hcut : z ∈ tsupport (rho ∘ b.symm)) : b.symm z ∈ K := by
  apply hsupport
  by_contra hn
  have hcont := b.symm.continuousOn.continuousAt (b.open_target.mem_nhds hz)
  have hzero : rho ∘ b.symm =ᶠ[𝓝 z] 0 :=
    (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto hcont
  exact (notMem_tsupport_iff_eventuallyEq.mpr hzero) hcut

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_quadratic_forcing_active_pair
#print axioms GlobalEmbedding.Continuation.actual_cutoff_inverse_support_on_target
