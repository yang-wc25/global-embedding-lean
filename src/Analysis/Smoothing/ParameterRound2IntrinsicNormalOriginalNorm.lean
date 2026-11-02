import Smoothing.ParameterRound2IntrinsicNormalImmersion
import Smoothing.ParameterRound2MeanNativeGerms
import Probes.ActualJointTensorChartTransfer

/-! The same intrinsic perturbed normal has the ORIGINAL source-first weighted
map norm. Actual adapted charts may differ with the atlas index; uniqueness of
the intrinsic projection binds every local construction to one native field.
The input bounds are first/Hessian/reference jets and TRUE joint transitions,
not bounds for the desired new normal. All numerical constants precede the
atlas, its cardinality, fields, domains and scale. Genuine open germs containing
the original samples suffice; original differentiation domains are unchanged. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Filter
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ}
local notation "Eparam" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Eparam × D
local notation "Y" => Fin (m+1+d) → ℝ
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

theorem parameterRound2_intrinsic_normal_original_weighted_norm
    (cF cT MH0 : ℝ) (hcF : 0 < cF) (hcT : 0 < cT) (hMH0 : 0 ≤ MH0) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ (j : ℕ) (MA MH Mv : ℝ)
      (T : ℕ → ℝ), 0 ≤ MA → 0 ≤ MH → 0 ≤ Mv → (∀ k, 0 ≤ T k) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ℕ)
      (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph Eparam Eparam)
      (F0 F : Eparam → M → V)
      (hF0 : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F0 p))
      (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
      (psi : Eparam → M → ℝ) (vref : Eparam × M → V)
      (e : (Fin A.count × Fin c) → Eparam → OpenPartialHomeomorph M D)
      (he : ∀ i p, e i p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
      (O : (Fin A.count × Fin c) → Set X)
      (U S : (Fin A.count × Fin c) → Set Y)
      (phi : (Fin A.count × Fin c) → Y → X)
      (_hO : ∀ i, IsOpen (O i)) (_hU : ∀ i, IsOpen (U i))
      (_hSU : ∀ i, S i ⊆ U i)
      (_hUorig : ∀ i, U i ⊆ incrementsOriginalDifferentiation A B i)
      (_hphi : ∀ i, ContDiffOn ℝ ∞ (phi i) (U i))
      (_hmap : ∀ i, MapsTo (phi i) (U i) (O i))
      (_hsame : ∀ i y, y ∈ U i →
        ((phi i y).1,(e i (phi i y).1).symm (phi i y).2) =
          incrementsOriginalJointPoint A B i y)
      (_hcoord : ∀ i z, z ∈ O i → z.2 ∈ (e i z.1).target)
      (_hpsi : ∀ i z, z ∈ O i →
        MDifferentiableAt 𝓙 𝓘(ℝ,ℝ) (psi z.1) ((e i z.1).symm z.2))
      (_hadapt : ∀ i z, z ∈ O i → psi z.1 ((e i z.1).symm z.2) = z.2 0)
      (_hJoint : ∀ i, ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e i z.1).symm z.2)) (O i))
      (_hvref : ∀ i, ContDiffOn ℝ ∞ (fun z : X => vref (z.1,(e i z.1).symm z.2)) (O i))
      (_hOldLegal : ∀ i z, z ∈ O i →
        ∃ normal : normalSpace (I := 𝓙) (F0 z.1) ((e i z.1).symm z.2),
        (normal : V) = vref (z.1,(e i z.1).symm z.2) ∧ ‖normal‖ = 1 ∧
        let xi := (tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi z.1 ((e i z.1).symm z.2))).toContinuousLinearMap.comp
          (mfderiv 𝓙 𝓘(ℝ,ℝ) (psi z.1) ((e i z.1).symm z.2))
        ∀ u w : xi.ker, inner ℝ
          ((trueSecondForm (F0 z.1) (hF0 z.1) ((e i z.1).symm z.2)
            (symmetricSquareProduct (TangentSpace 𝓙 ((e i z.1).symm z.2)) u.val w.val)) : V)
          (normal : V) = 0)
      (_hFirst : ∀ i z, z ∈ O i → ∀ w : D,
        cF*‖w‖^2 ≤ ‖fderiv ℝ (F0 z.1 ∘ (e i z.1).symm) z.2 w‖^2)
      (_hFrame : ∀ i z, z ∈ O i → ∀ w : Tdata, cT*‖w‖^2 ≤
        ‖incrementsModeAmbientTransverseFrame (F0 z.1) (hF0 z.1) (e i z.1).symm z.2 w‖^2)
      (_hHessian0 : ∀ i z, z ∈ O i →
        ‖fderiv ℝ (fderiv ℝ (F0 z.1 ∘ (e i z.1).symm)) z.2‖ ≤ MH0)
      (_hD : ∀ i z, z ∈ O i → ‖fderiv ℝ (F0 z.1 ∘ (e i z.1).symm) z.2-
        fderiv ℝ (F z.1 ∘ (e i z.1).symm) z.2‖ ≤ epsilon)
      (_hH : ∀ i z, z ∈ O i → ‖fderiv ℝ (fderiv ℝ (F z.1 ∘ (e i z.1).symm)) z.2-
        fderiv ℝ (fderiv ℝ (F0 z.1 ∘ (e i z.1).symm)) z.2‖ ≤ epsilon)
      (ell : ℝ) (_hell : 0 < ell) (_hell1 : ell ≤ 1),
      (∀ i k, k ≤ j → ∀ y ∈ S i, ell^k*‖iteratedFDeriv ℝ k
        (fun z : X => fderiv ℝ (F z.1 ∘ (e i z.1).symm) z.2) (phi i y)‖ ≤ MA) →
      (∀ i k, k ≤ j → ∀ y ∈ S i, ell^k*‖iteratedFDeriv ℝ k
        (fun z : X => fderiv ℝ (fderiv ℝ (F z.1 ∘ (e i z.1).symm)) z.2) (phi i y)‖ ≤ MH) →
      (∀ i k, k ≤ j → ∀ y ∈ S i, ell^k*‖iteratedFDeriv ℝ k
        (fun z : X => vref (z.1,(e i z.1).symm z.2)) (phi i y)‖ ≤ Mv) →
      (∀ i k, 1 ≤ k → k ≤ j → ∀ y ∈ S i,
        ell^(k-1)*‖iteratedFDeriv ℝ k (phi i) y‖ ≤ T k) →
      let normal := parameterRound2_intrinsicUnitFreeNormalField F hF psi vref
      (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B normal i) (U i)) ∧
      paperAtlasWeighted 0 j ell (incrementsOriginalMapCoordinates A B normal)
        (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
      (paperAtlasWeighted 0 j ell (incrementsOriginalMapCoordinates A B normal)
        (incrementsOriginalDifferentiation A B) S).toReal ≤ C := by
  obtain ⟨epsilon,hepsilon,hprep⟩ := parameterRound2_intrinsic_normal_and_immersion_preparation
    (m := m) (N := N) (Ep := Eparam) (M := M) cF cT MH0 hcF hcT hMH0
  refine ⟨epsilon,hepsilon,?_⟩
  intro j MA MH Mv T hMA hMH hMv hT
  obtain ⟨K,hK,hprepK⟩ := hprep j MA MH Mv hMA hMH hMv
  let cy := (EuclideanSpace.equiv (Fin N) ℝ).toContinuousLinearMap
  let Kobs := ‖cy‖*actualFastChartTransferPrefix T j*K
  have hKobs : 0 ≤ Kobs := mul_nonneg
    (mul_nonneg (norm_nonneg _) (actualFastChartTransferPrefix_nonneg T hT j)) hK
  refine ⟨(j+1)*Kobs,mul_nonneg (by positivity) hKobs,?_⟩
  intro c A B F0 F hF0 hF psi vref e he O U S phi hO hU hSU hUorig hphi hmap
    hsame hcoord hpsi hadapt hJoint hvref hOldLegal hFirst hFrame hHessian0 hD hH
    ell hell hell1 hAj hHj hvj hphij
  let normal := parameterRound2_intrinsicUnitFreeNormalField F hF psi vref
  let f := fun i (z : X) => normal (z.1,(e i z.1).symm z.2)
  have hlocal (i : Fin A.count × Fin c) :
      ContDiffOn ℝ ∞ (f i) (O i) ∧
      ∀ k ≤ j, ∀ y ∈ S i, ell^k*‖iteratedFDeriv ℝ k (f i) (phi i y)‖ ≤ K := by
    have hSO : phi i '' S i ⊆ O i := by
      rintro _ ⟨y,hy,rfl⟩
      exact hmap i (hSU i hy)
    have h := hprepK F0 F hF0 hF psi (e i) (he i) (O i) (phi i '' S i)
      (hO i) hSO (hcoord i) (hpsi i) (hadapt i) (hJoint i) vref (hvref i)
      (hOldLegal i) (hFirst i) (hFrame i) (hHessian0 i) (hD i) (hH i) ell hell
      (by rintro k hk _ ⟨y,hy,rfl⟩; exact hAj i k hk y hy)
      (by rintro k hk _ ⟨y,hy,rfl⟩; exact hHj i k hk y hy)
      (by rintro k hk _ ⟨y,hy,rfl⟩; exact hvj i k hk y hy)
    exact ⟨h.2.1,fun k hk y hy => h.2.2.2 k hk _ ⟨y,hy,rfl⟩⟩
  have heq (i) : EqOn (incrementsOriginalMapCoordinates A B normal i)
      (cy ∘ f i ∘ phi i) (U i) := by
    intro y hy
    exact congrArg (fun z => cy (normal z)) (hsame i y hy).symm
  have hreg (i) : ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B normal i) (U i) :=
    (cy.contDiff.comp_contDiffOn ((hlocal i).1.comp (hphi i) (hmap i))).congr (heq i)
  have hb (i) (k : ℕ) (hk : k ≤ j) (y : Y) (hy : y ∈ S i) :
      ell^k*‖iteratedFDeriv ℝ k (incrementsOriginalMapCoordinates A B normal i) y‖ ≤ Kobs := by
    have hc := actual_fast_joint_chart_transfer T hT k (phi i) (f i) (U i) (O i)
      (hU i) (hO i) (hphi i) (hlocal i).1 (hmap i) y (hSU i hy) ell ell K hell le_rfl
      (fun r hr => (hlocal i).2 r (hr.trans hk) y hy)
      (fun r hr hrk => hphij i r hr (hrk.trans hk) y hy)
    have hc' : ell^k*‖iteratedFDeriv ℝ k (f i ∘ phi i) y‖ ≤
        actualFastChartTransferPrefix T j*K := hc.trans
      (mul_le_mul_of_nonneg_right (actualFastChartTransferCost_le_prefix T hT hk) hK)
    have hl := slow_linear_jet_bound cy (U i) (hU i) (f i ∘ phi i)
      ((hlocal i).1.comp (hphi i) (hmap i)) k ell
      (actualFastChartTransferPrefix T j*K) hell.le y (hSU i hy) hc'
    have hg := eventuallyEq_of_mem ((hU i).mem_nhds (hSU i hy)) (fun z hz => heq i hz)
    rw [(hg.iteratedFDeriv ℝ k).eq_of_nhds]
    exact hl.trans_eq (by dsimp only [Kobs]; ring)
  have hout := parameterRound2_paperAtlasWeighted_le_of_weighted_jets j ell Kobs hell hell1 hKobs
    (incrementsOriginalMapCoordinates A B normal) U S hU hSU hreg hb
  have hr := actual_paperAtlasWeighted_open_restrict 0 j ell
    (incrementsOriginalMapCoordinates A B normal) (incrementsOriginalDifferentiation A B) U S
    (parameterRound2_originalDifferentiation_open A B) hU hUorig hSU
  refine ⟨hreg,?_⟩
  rw [hr]
  exact hout

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.parameterRound2_intrinsic_normal_original_weighted_norm
