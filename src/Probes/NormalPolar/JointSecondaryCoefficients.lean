import NormalPolar.JointSecondaryAmplitude
import NormalPolar.ParameterDisplacementPrescribedVariableCoefficient
import NormalPolar.ActualRepairModelFirstDefectCoefficientSum

/-! One coefficient bound for the actual joint background/prescribed array.

All derivatives in Ep are real joint derivatives. The parameter field u is
inserted into the finite prescribed columns before differentiation. Background
input is one tensor field on the same Ep; it may be the actual joint iterate.
The uniform constant is selected before maps, scales and parameter fields.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {E H M Ep Tr : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  {m N p r : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

theorem jointSecondary_variable_prescribed_coefficient_cost_nonneg
    (m N p n length j : ℕ) (T : ℕ → ℝ)
    (weight Mg Bchi Bnu Mphase Ku : ℝ) (hT : ∀ k, 0 ≤ T k)
    (hMg : 0 ≤ Mg) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu)
    (hMphase : 0 ≤ Mphase) (hKu : 0 ≤ Ku) :
    0 ≤ actualVariablePrescribedCoefficientCost m N p n length j T weight Mg Bchi Bnu Mphase Ku := by
  unfold actualVariablePrescribedCoefficientCost
  exact mul_nonneg (by positivity)
    (actualRepairModelFirstDefect_prescribed_coefficient_cost_nonneg
      m N n length j T weight Mg Bchi Bnu Mphase 1 hT hMg hBchi hBnu hMphase zero_le_one)

theorem jointSecondary_common_coefficients_from_raw_uniform
    (n q probeLength j Rsub Lprimary : ℕ) (hq : 1 ≤ q)
    (hbackgroundOrder : j+2+(q+2) ≤ n) (hprobeOrder : j+2+probeLength ≤ n)
    (reserve Bnd Mg Bchi Bnu Ku Mphase : ℝ)
    (hreserve : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu) (hKu : 0 ≤ Ku) (hMphase : 0 ≤ Mphase)
    (weight : Fin r → ℝ) (Tbackground Tprobe : ℕ → ℝ)
    (hTbackground : ∀ k, 0 ≤ Tbackground k) (hTprobe : ∀ k, 0 ≤ Tprobe k) :
    ∃ MD : ℝ, 0 ≤ MD ∧ ∀
      (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
      (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
      (label : (Fin r × Bool) ↪ Fin p)
      (c : Fin r → Ep → D → M) (chi : Fin r → X → ℝ)
      (nu : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l b x))
      (a : Fin r → OpenPartialHomeomorph (Ep × M) X) (phase : Fin r → Ep × M → ℝ)
      (input inputbar : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
      (tau ell delta Delta : ℝ) (hdelta : 0 ≤ delta)
      (W : Set (Ep × M)) (K : (Λ ⊕ Fin r) → Set (Ep × M))
      (e : OpenPartialHomeomorph M D)
      (he : ContMDiffOn I 𝓘(ℝ,D) ∞ e e.source)
      (heInv : ContMDiffOn 𝓘(ℝ,D) I ∞ e.symm e.target)
      (Omega S : Set X)
      (background : ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n (q+2) j Rsub Lprimary
        reserve Bnd Mg Tbackground F hF g input inputbar W (fun l => K (Sum.inl l)) e Omega S tau ell Delta)
      (hTarget : ∀ z ∈ Omega, z.2 ∈ e.target)
      (prescribed : ActualPrescribedObservationProfiles F hF c chi nu a W (fun l => K (Sum.inr l))
        n (j+1) ell Mg Bchi Bnu (fun z : X => (z.1,e.symm z.2)) Omega S Tprobe phase Mphase)
      (u : Ep → Fin p → ℝ)
      (hu : ContDiffOn ℝ ∞ (fun z : X => u z.1) Omega)
      (hub : ∀ k ≤ j, ∀ z ∈ S,
        ell^k*‖iteratedFDeriv ℝ k (fun y : X => u y.1) z‖ ≤ Ku),
    let vf := fun l => actualProbeNormalAmplitude F (c l) (chi l) (nu l) delta tau (weight l)
    let phases := Sum.elim g.phase phase
    let R := jointSecondaryCombinedAmplitude F hF g label c vf tau delta (q+2) probeLength a input u false
    let Q := jointSecondaryCombinedAmplitude F hF g label c vf tau delta (q+2) probeLength a input u true
    let coeff := fun l z => incrementsSecondaryPhysicalCoefficient
      (fun l b x => phases l (b,e.symm x)) tau (fun (_ : Λ ⊕ Fin r) (_ : Ep) (_ : Unit) _ => 1)
      (fun l b (_ : Unit) x => R l (b,e.symm x)) (fun l b (_ : Unit) x => Q l (b,e.symm x))
      (fun i _ => EuclideanSpace.single i 1) z l
    ∀ l, ContDiffOn ℝ ∞ (coeff l) Omega ∧
      (∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k (coeff l) z‖ ≤ MD*|delta|) := by
  obtain ⟨Mbackground,hMbackground,hbg⟩ := actualRepairModelFirstDefect_background_unit_coefficients_from_raw_uniform
    (I := I) (M := M) (Ep := Ep) (Tr := Tr) (m := m) (N := N)
    n q j Rsub Lprimary hq hbackgroundOrder reserve Bnd Mg hreserve hBnd hMg Tbackground hTbackground
  let Cprobe := fun l => actualVariablePrescribedCoefficientCost
    m N p n probeLength j Tprobe (weight l) Mg Bchi Bnu Mphase Ku
  have hCprobe (l : Fin r) : 0 ≤ Cprobe l :=
    jointSecondary_variable_prescribed_coefficient_cost_nonneg m N p n probeLength j Tprobe
      (weight l) Mg Bchi Bnu Mphase Ku hTprobe hMg hBchi hBnu hMphase hKu
  let MD := Mbackground+∑ l, Cprobe l
  have hsum : 0 ≤ ∑ l, Cprobe l := Finset.sum_nonneg (fun l _ => hCprobe l)
  have hM : Mbackground ≤ MD := le_add_of_nonneg_right hsum
  have hP (l : Fin r) : Cprobe l ≤ MD :=
    (Finset.single_le_sum (fun l _ => hCprobe l) (Finset.mem_univ l)).trans (le_add_of_nonneg_left hMbackground)
  refine ⟨MD,add_nonneg hMbackground hsum,?_⟩
  intro F hF g label c chi nu a phase input inputbar tau ell delta Delta hdelta W K e he heInv Omega S
    background hTarget prescribed u hu hub vf phases R Q coeff
  have hobs : ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod I) ∞ (fun z : X => (z.1,e.symm z.2)) Omega := by
    have hf : ContMDiffOn 𝓘(ℝ,X) 𝓘(ℝ,Ep) ∞ (fun z : X => z.1) Omega := contDiffOn_fst.contMDiffOn
    have hs : ContMDiffOn 𝓘(ℝ,X) 𝓘(ℝ,D) ∞ (fun z : X => z.2) Omega := contDiffOn_snd.contMDiffOn
    exact hf.prodMk (heInv.comp hs (fun z hz => hTarget z hz))
  have hp := actual_prescribed_variable_coefficient_from_raw label F hF c chi nu a W
    (fun l => K (Sum.inr l)) background.prim.hW n probeLength j hprobeOrder tau ell delta weight
    Mg Bchi Bnu Mphase Ku background.htau background.htaul background.hell1 hMg hdelta hBchi hBnu
    hMphase hKu (fun z : X => (z.1,e.symm z.2)) Omega S background.hO background.hSO hobs background.hmapWO
    Tprobe hTprobe phase prescribed (fun z : X => u z.1) hu hub
  intro l
  cases l with
  | inl l =>
    have hb := hbg F hF g input inputbar W (fun l => K (Sum.inl l)) e he heInv Omega S
      tau ell Delta background hTarget delta l
    refine ⟨hb.1,?_⟩
    intro k hk z hz
    exact (hb.2.1 k hk z hz).trans (mul_le_mul_of_nonneg_right hM (abs_nonneg delta))
  | inr l =>
    refine ⟨(hp l).1,?_⟩
    intro k hk z hz
    exact ((hp l).2 k hk z hz).trans
      ((mul_le_mul_of_nonneg_right (hP l) hdelta).trans_eq (by rw [abs_of_nonneg hdelta]))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondary_common_coefficients_from_raw_uniform
