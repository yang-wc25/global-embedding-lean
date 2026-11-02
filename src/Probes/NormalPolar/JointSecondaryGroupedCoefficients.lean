import NormalPolar.JointSecondaryGroupedProfiles
import NormalPolar.ParameterDisplacementPrescribedVariableCoefficient

/-!
# Complete joint coefficients of the grouped original prescribed wave

Each subordinate piece is reconstructed by the actual finite solver. Their
coefficients are then summed within the original label. The raw producer
below proves all slow joint derivatives after substituting the same variable
parameter, retaining both channels and inactive zero germs. Its explicit
constant depends only on fixed primitive budgets and the fixed finite pieces.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

theorem jointGrouped_diagonal_coefficient_sum
    {Eq SIdx : Type*} [NormedAddCommGroup Eq] [NormedSpace ℝ Eq] [Fintype SIdx]
    {m N p : ℕ}
    (phase : Eq × EuclideanSpace ℝ (Fin (m+1)) → ℝ) (tau : ℝ)
    (amp : SIdx → Bool → (Fin p → ℝ) → Eq × EuclideanSpace ℝ (Fin (m+1)) →
      EuclideanSpace ℝ (Fin N))
    (Omega : Set (Eq × EuclideanSpace ℝ (Fin (m+1)))) (hOmega : IsOpen Omega)
    (u : Fin p → ℝ)
    (hamp : ∀ s ch, ContDiffOn ℝ ∞ (amp s ch u) Omega)
    (z : Eq × EuclideanSpace ℝ (Fin (m+1))) (hz : z ∈ Omega) :
    actualDiagonalPhysicalCoefficient phase tau (fun ch v y => ∑ s, amp s ch v y) u z =
      ∑ s, actualDiagonalPhysicalCoefficient phase tau (amp s) u z := by
  have hd (s : SIdx) (ch : Bool) :
      DifferentiableAt ℝ (fun x => amp s ch u (z.1,x)) z.2 :=
    ((actual_joint_contDiffOn_slice _ Omega (hamp s ch) z.1).contDiffAt
      ((hOmega.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz)).differentiableAt (by simp)
  funext i
  simpa only [actualDiagonalPhysicalCoefficient,Finset.sum_apply] using
    round4_primary_coefficient_sum (fun x => phase (z.1,x)) tau (fun (_ : Unit) _ => 1)
      (fun s (_ : Unit) x => amp s false u (z.1,x))
      (fun s (_ : Unit) x => amp s true u (z.1,x)) z.2 (EuclideanSpace.single i 1)
      (fun s _ => hd s false) (fun s _ => hd s true)

variable {E H M Ep Eq : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Eq] [NormedSpace ℝ Eq]
  {m N p r : ℕ} {Sub : Fin r → Type*} [∀ l, Fintype (Sub l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Y" => Eq × D

theorem jointGrouped_prescribed_coefficient_from_raw
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : (l : Fin r) → Sub l → Ep → D → M)
    (chi : (l : Fin r) → Sub l → X → ℝ)
    (nu : (l : Fin r) → (s : Sub l) → (b : Ep) → (x : D) →
      normalSpace (I := I) (F b) (c l s b x))
    (a : (l : Fin r) → Sub l → OpenPartialHomeomorph (Ep × M) X)
    (W : Set (Ep × M)) (pieceK : (l : Fin r) → Sub l → Set (Ep × M))
    (hW : IsOpen W) (n length j : ℕ) (horder : j+2+length ≤ n)
    (tau ell delta : ℝ) (weight : Fin r → ℝ) (Mg Bchi Bnu Mphase Ku : ℝ)
    (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hMg : 0 ≤ Mg) (hdelta : 0 ≤ delta) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu)
    (hMphase : 0 ≤ Mphase) (hKu : 0 ≤ Ku)
    (kappa : Y → Ep × M) (Omega S : Set Y) (hOmega : IsOpen Omega) (hS : S ⊆ Omega)
    (hkappa : ContMDiffOn 𝓘(ℝ,Y) ((𝓘(ℝ,Ep)).prod I) ∞ kappa Omega)
    (hmap : MapsTo kappa Omega W) (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (phase : Fin r → Ep × M → ℝ)
    (profiles : JointGroupedPrescribedObservationProfiles F hF c chi nu a W pieceK n (j+1)
      ell Mg Bchi Bnu kappa Omega S T phase Mphase)
    (u : Y → Fin p → ℝ) (hu : ContDiffOn ℝ ∞ u Omega)
    (hub : ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k u z‖ ≤ Ku) :
    let vf := fun l s => actualProbeNormalAmplitude F (c l s) (chi l s) (nu l s) delta tau (weight l)
    let amp := fun l ch v z => jointGroupedPrescribedAmplitude ch label F hF c vf tau length a v l (kappa z)
    ∀ l, let f := fun z => actualDiagonalPhysicalCoefficient (phase l ∘ kappa) tau (amp l) (u z) z
      ContDiffOn ℝ ∞ f Omega ∧ ∀ k ≤ j, ∀ z ∈ S,
        ell^k*‖iteratedFDeriv ℝ k f z‖ ≤
          ((Fintype.card (Sub l) : ℝ)*actualVariablePrescribedCoefficientCost m N p n length j
            T (weight l) Mg Bchi Bnu Mphase Ku)*delta := by
  intro vf amp l f
  let pieces := fun (s : Sub l) ch v z => round4PrescribedGlobalAmplitude ch label l F hF
    (c l s) (vf l s) tau length (a l s) v (kappa z)
  let coeff := fun s z => actualDiagonalPhysicalCoefficient (phase l ∘ kappa) tau (pieces s) (u z) z
  let C := actualVariablePrescribedCoefficientCost m N p n length j
    T (weight l) Mg Bchi Bnu Mphase Ku
  have hpiece (s : Sub l) : ContDiffOn ℝ ∞ (coeff s) Omega ∧
      ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k (coeff s) z‖ ≤ C*delta := by
    exact actual_prescribed_variable_coefficient_from_raw label F hF
      (fun _ : Fin r => c l s) (fun _ : Fin r => chi l s) (fun _ : Fin r => nu l s)
      (fun _ : Fin r => a l s) W (fun _ : Fin r => pieceK l s) hW n length j horder
      tau ell delta (fun _ : Fin r => weight l) Mg Bchi Bnu Mphase Ku
      htau htaul hell1 hMg hdelta hBchi hBnu hMphase hKu
      kappa Omega S hOmega hS hkappa hmap T hT (fun _ : Fin r => phase l)
      (profiles.single F hF c chi nu a W pieceK n (j+1) ell Mg Bchi Bnu
        kappa Omega S T phase Mphase l s) u hu hub l
  have hamp (s : Sub l) (ch : Bool) (v : Fin p → ℝ) :
      ContDiffOn ℝ ∞ (pieces s ch v) Omega :=
    ((actualRepairModelFirstDefect_prescribed_amplitude_regular ch label l F hF
      (c l s) (chi l s) (nu l s) (a l s) W (pieceK l s) hW n (j+1) length
      ell Mg Bchi Bnu tau delta (weight l) (profiles.raw l s) v).1.comp hkappa hmap).contDiffOn
  have he : EqOn f (fun z => ∑ s, coeff s z) Omega := by
    intro z hz
    exact jointGrouped_diagonal_coefficient_sum (phase l ∘ kappa) tau pieces Omega hOmega
      (u z) (fun s ch => hamp s ch (u z)) z hz
  have hs : ContDiffOn ℝ ∞ (fun z => ∑ s, coeff s z) Omega :=
    ContDiffOn.sum (fun s _ => (hpiece s).1)
  refine ⟨hs.congr he,?_⟩
  intro k hk z hz
  rw [((he.eventuallyEq_of_mem (hOmega.mem_nhds (hS hz))).iteratedFDeriv ℝ k).eq_of_nhds]
  rw [iteratedFDeriv_fun_sum_apply
    (fun s _ => ((hpiece s).1.contDiffAt (hOmega.mem_nhds (hS hz))).of_le (by simp))]
  calc
    _ ≤ ell^k*∑ s, ‖iteratedFDeriv ℝ k (coeff s) z‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg (htau.trans_le htaul).le k)
    _ = ∑ s, ell^k*‖iteratedFDeriv ℝ k (coeff s) z‖ := by rw [Finset.mul_sum]
    _ ≤ ∑ _s : Sub l, C*delta := Finset.sum_le_sum (fun s _ => (hpiece s).2 k hk z hz)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; dsimp only [C]; ring

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.jointGrouped_diagonal_coefficient_sum
#print axioms GlobalEmbedding.Continuation.jointGrouped_prescribed_coefficient_from_raw
