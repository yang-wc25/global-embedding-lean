import NormalPolar.GlobalWaveResponseBackgroundGlobalRestriction
import NormalPolar.GlobalWaveResponseBackgroundNativeC1
import NormalPolar.GlobalWaveResponseBackgroundJoint

/-! Sharp original-background native first-spatial-jet parameter response
from primitive raw pairs. Source/free/reconstruction/observer/support budgets
are produced internally. A common positive parameter neighborhood is explicit
and is never inferred from unrelated pair-specific positive neighborhoods. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Continuation
variable {P E H M Ep Tr : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep×D

private local instance bgGlobalHessianSemi : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance bgGlobalHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance bgGlobalHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace

theorem globalWave_background_global_native_first_response
    (n length j Rsub Lprimary : ℕ) (horder : j+1+length ≤ n) (hj : 2 ≤ j)
    (reserve Bnd Mg : ℝ) (hc : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Λ Β : Type*} [Fintype Λ] [Fintype Β]
      (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
      (g : IncrementsGlobalPrimaryFamily (I:=I) (m:=m) (N:=N) (Λ:=Λ) (Β:=Β) F)
      (input : P → (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
      (Su : Set P) (hSu : IsOpen Su) (u : P) (hu : u ∈ Su)
      (W : Set (Ep×M)) (primary : Λ → Set (Ep×M))
      (inputRef : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
      (base : ParameterRound2GlobalMeanPrimitives F hF g inputRef W primary)
      (hArgument : ∀ nu, ContMDiffOn ((𝓘(ℝ,P×Ep)).prod I) 𝓘(ℝ,ℝ) ∞
        (fun z : (P×Ep)×M => g.linearArgument nu z.1.2 z.2 (input z.1.1 z.1.2 z.2))
        ((((fun z : (P×Ep)×M => z.1.1) ⁻¹' Su) ∩
          ((fun z : (P×Ep)×M => (z.1.2,z.2)) ⁻¹' W)) ∩
          ((fun z : (P×Ep)×M => (z.1.2,z.2)) ⁻¹' primary nu)))
      (hPositive : ∀ v ∈ Su, ∀ nu z, z ∈ incrementsGlobalRelativeSupport W (g.cutoff nu) →
        0 < g.linearArgument nu z.1 z.2 (input v z.1 z.2))
      (hadapt : ∀ nu beta z, z ∈ (g.chart nu beta).source →
        g.phase nu z = (g.chart nu beta z).2 0)
      (e : OpenPartialHomeomorph M D)
      (he : ContMDiffOn 𝓘(ℝ,D) I ∞ e.symm e.target)
      (O Samples : Set X) (hO : IsOpen O) (hSO : Samples ⊆ O)
      (htarget : ∀ y ∈ O, y.2 ∈ e.target)
      (hmap : MapsTo (fun y : X => (y.1,e.symm y.2)) O W)
      (tau ell Dinput : ℝ) (htau : 0 < tau) (hDinput : 0 ≤ Dinput)
      (rawPair : ∀ v ∈ Su, ∃ (G : Set (Ep×M)) (hG : IsOpen G) (Oraw : Set X) (Delta : ℝ),
        Nonempty (ParameterRound2GlobalMeanRawProfiles (Tr:=Tr) n length j Rsub Lprimary reserve Bnd Mg T
          F hF (parameterRound2_restrictPrimaryFamily F g G hG) (input v) (input u)
          G primary e Oraw Samples tau ell Delta) ∧
        Delta ≤ Dinput*(‖v‖+‖u‖)*‖v-u‖),
    ∀ y ∈ Samples,
    let f := fun v x => incrementsGlobalPrimaryWave F hF g (input v) length tau (y.1,e.symm x)
    HasFDerivAt (fun v => fderiv ℝ (f v) y.2)
      (fderiv ℝ (fun v => fderiv ℝ (f v) y.2) u) u ∧
      ‖fderiv ℝ (fun v => fderiv ℝ (f v) y.2) u‖ ≤ 2*(C*Dinput)*‖u‖ := by
  obtain ⟨C,hC,hDiff⟩ := globalWave_background_global_difference_at_fixed_sample
    (I:=I) (M:=M) (Ep:=Ep) (Tr:=Tr) (m:=m) (N:=N) n length j Rsub Lprimary horder
      reserve Bnd Mg hc hBnd hMg T hT
  refine ⟨C,hC,?_⟩
  intro Λ Β _ _ F hF g input Su hSu u hu W primary inputRef base hArgument hPositive hadapt
    e he O Samples hO hSO htarget hmap tau ell Dinput htau hDinput rawPair y hy f
  have hglobal := globalWave_background_global_joint_from_primitive F hF g input inputRef
    Su hSu W primary base hArgument hPositive length tau
  let Ω : Set ((P×Ep)×D) := {z | z.1.1 ∈ Su ∧ (z.1.2,z.2) ∈ O}
  have hObs : ContMDiffOn 𝓘(ℝ,(P×Ep)×D) ((𝓘(ℝ,P×Ep)).prod I) ∞
      (fun z : (P×Ep)×D => (z.1,e.symm z.2)) Ω :=
    contDiff_fst.contMDiff.contMDiffOn.prodMk
      (he.comp contDiff_snd.contMDiff.contMDiffOn (fun z hz => htarget _ hz.2))
  have hJoint : ContDiffOn ℝ ∞ (fun z : (P×Ep)×D =>
      incrementsGlobalPrimaryWave F hF g (input z.1.1) length tau (z.1.2,e.symm z.2)) Ω :=
    (hglobal.comp hObs (fun z hz => ⟨hz.1,hmap hz.2⟩)).contDiffOn
  let full := fun v (z : X) => incrementsGlobalPrimaryWave F hF g (input v) length tau (z.1,e.symm z.2)
  have hpair : ∀ v ∈ Su, ∀ k ≤ 2, tau^k*‖iteratedFDeriv ℝ k
      (fun x => full v x-full u x) y‖ ≤ (C*Dinput)*tau*(‖v‖+‖u‖)*‖v-u‖ := by
    intro v hv k hk
    obtain ⟨G,hG,Oraw,Delta,⟨raw⟩,hDelta⟩ := rawPair v hv
    have hb := (hDiff F hF g (input v) (input u) G hG primary e Oraw Samples tau ell Delta raw
      hadapt).2 k (hk.trans hj) y hy
    calc
      _ ≤ C*tau*Delta := hb
      _ ≤ C*tau*(Dinput*(‖v‖+‖u‖)*‖v-u‖) := mul_le_mul_of_nonneg_left hDelta (by positivity)
      _ = _ := by ring
  exact globalWave_native_background_first_of_fast_difference full Su O hSu hO hJoint
    u hu y (hSO hy) tau (C*Dinput) htau (mul_nonneg hC hDinput) hpair

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.globalWave_background_global_native_first_response
