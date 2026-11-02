import Probes.Round4PrescribedGlobalMeanDifference
import Probes.Round4PrescribedOriginalMeanCoordinates

/-!
# Original atlas tensor seminorm of the actual global prescribed mean difference

Every observer uses the original parameter inverse chart and source inverse
chart. Primitive source/transition/phase profiles produce actual all-joint mean
difference jets with the true active support multiplicity. The SAME native
tensor is then transferred to the unchanged source-first paper seminorm and its
original differentiation domains. The finite Pi step contributes no atlas or
parameter-cardinality loss. No bound on the produced mean or its coordinate
derivatives is a premise.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N p r count : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Pspace" => Fin p → ℝ
local notation "𝓙" => 𝓘(ℝ,D)

def round4OriginalObserver (atlas : BufferedAtlas M D)
    (param : Fin count → OpenPartialHomeomorph Ep Ep) (idx : Fin atlas.count × Fin count) (z : X) : Ep × M :=
  ((param idx.2).symm z.1,(atlas.chart idx.1).symm z.2)

def round4OriginalTensorDirections (k : Fin ((m+1)*(m+1))) (s : Bool) : D :=
  if s then EuclideanSpace.single (finProdFinEquiv.symm k).2 1
    else EuclideanSpace.single (finProdFinEquiv.symm k).1 1

theorem round4_prescribed_original_mean_difference_norm
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M) (chi : Fin r → X → ℝ)
    (nu : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I:=𝓙) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (W : Set (Ep × M)) (K : Fin r → Set (Ep × M)) (hW : IsOpen W)
    (hK : ∀ l, IsClosed (Subtype.val ⁻¹' K l : Set W)) (hKsource : ∀ l, K l ⊆ (a l).source)
    (hchart : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,X) ∞ (a l) (a l).source)
    (hinput : ∀ l z, z ∈ (a l).target → z ∈ tsupport (chi l) → (a l).symm z ∈ K l)
    (n length j : ℕ) (horder : j+2+length ≤ n)
    (Slocal : Fin r → Set X) (hSloc : ∀ l, Slocal l ⊆ (a l).target)
    (hA : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hB : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hG : ∀ l, ContDiffOn ℝ ∞ (fun z : X => freeGramRightInverse (fderiv ℝ (F z.1 ∘ c l z.1) z.2)) (a l).target)
    (hJ : ∀ l, ContDiffOn ℝ ∞ (fun z : X => (normalSpace (I:=𝓙) (F z.1) (c l z.1 z.2)).subtypeL.comp
      (incrementsModeCoordinateJ (F z.1) (hF z.1) (c l z.1) z.2)) (a l).target)
    (hT : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeTransverseValue (F z.1) (c l z.1) z.2) (a l).target)
    (hBR : ∀ l, ContDiffOn ℝ ∞ (fun z : X => fun d : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c l z.1) z.2 0 d : V)) (a l).target)
    (hchi : ∀ l, ContDiffOn ℝ ∞ (chi l) (a l).target)
    (hnu : ∀ l, ContDiffOn ℝ ∞ (fun z : X => (nu l z.1 z.2 : V)) (a l).target)
    (tau ell delta Mg Mp : ℝ) (weight Bchi Bnu : Fin r → ℝ)
    (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hMg : 0 ≤ Mg) (hdelta : 0 ≤ delta) (hMp : 0 ≤ Mp)
    (hBchi : ∀ l, 0 ≤ Bchi l) (hBnu : ∀ l, 0 ≤ Bnu l)
    (hAb : ∀ l k, k ≤ n → ∀ z ∈ Slocal l, ell^k*‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeComplexFirstOrderA (F w.1) (hF w.1) (c l w.1) w.2) z‖ ≤ Mg)
    (hBb : ∀ l k, k ≤ n → ∀ z ∈ Slocal l, ell^k*‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeComplexFirstOrderB (F w.1) (hF w.1) (c l w.1) w.2) z‖ ≤ Mg)
    (hGb : ∀ l k, k ≤ j+1 → ∀ z ∈ Slocal l, ell^k*‖iteratedFDeriv ℝ k
      (fun w : X => freeGramRightInverse (fderiv ℝ (F w.1 ∘ c l w.1) w.2)) z‖ ≤ Mg)
    (hJb : ∀ l k, k ≤ j+1 → ∀ z ∈ Slocal l, ell^k*‖iteratedFDeriv ℝ k
      (fun w : X => (normalSpace (I:=𝓙) (F w.1) (c l w.1 w.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F w.1) (hF w.1) (c l w.1) w.2)) z‖ ≤ Mg)
    (hTb : ∀ l k, k ≤ j+1 → ∀ z ∈ Slocal l, ell^k*‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeTransverseValue (F w.1) (c l w.1) w.2) z‖ ≤ Mg)
    (hBRb : ∀ l k, k ≤ n → ∀ z ∈ (a l).target, ell^k*‖iteratedFDeriv ℝ k
      (fun w : X => fun d : Fin (m+1) =>
        (incrementsModeSecondForm (F w.1) (hF w.1) (c l w.1) w.2 0 d : V)) z‖ ≤ Mg)
    (hchib : ∀ l k, k ≤ n → ∀ z ∈ (a l).target, ell^k*‖iteratedFDeriv ℝ k (chi l) z‖ ≤ Bchi l)
    (hnub : ∀ l k, k ≤ n → ∀ z ∈ (a l).target, ell^k*‖iteratedFDeriv ℝ k
      (fun w : X => (nu l w.1 w.2 : V)) z‖ ≤ Bnu l)
    (hphaseGlobal : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (phase l) W)
    (atlas : BufferedAtlas M D) (param : Fin count → OpenPartialHomeomorph Ep Ep)
    (hAtlas : IsSmoothBufferedAtlas atlas)
    (Samples : Fin atlas.count × Fin count → Set (Fin (m+1+d) → ℝ))
    (Omega : Fin atlas.count × Fin count → Set X) (hOmega : ∀ idx, IsOpen (Omega idx))
    (hOmegaSub : ∀ idx, Omega idx ⊆ (param idx.2).target ×ˢ (atlas.chart idx.1).target)
    (hSamples : ∀ idx, (parameterTensorModelEquiv (m+1) d) ⁻¹' Samples idx ⊆ Omega idx)
    (hmap : ∀ idx, MapsTo (round4OriginalObserver atlas param idx) (Omega idx) W)
    (Obs : (Fin atlas.count × Fin count) → Fin r → Set X) (hObs : ∀ idx l, IsOpen (Obs idx l))
    (hactive : ∀ idx l, Omega idx ∩ (round4OriginalObserver atlas param idx) ⁻¹' K l ⊆ Obs idx l)
    (hsource : ∀ idx l, MapsTo (round4OriginalObserver atlas param idx) (Obs idx l) (a l).source)
    (htransition : ∀ idx l, ContDiffOn ℝ ∞ (a l ∘ round4OriginalObserver atlas param idx) (Obs idx l))
    (hsample : ∀ idx l z, parameterTensorModelEquiv (m+1) d z ∈ Samples idx →
      round4OriginalObserver atlas param idx z ∈ K l →
      a l (round4OriginalObserver atlas param idx z) ∈ Slocal l)
    (T : (Fin atlas.count × Fin count) → Fin r → ℕ → ℝ) (hTprof : ∀ idx l k, 0 ≤ T idx l k)
    (htransitionb : ∀ idx l k, 1 ≤ k → k ≤ j+1 → ∀ z : X,
      parameterTensorModelEquiv (m+1) d z ∈ Samples idx → round4OriginalObserver atlas param idx z ∈ K l →
      ell^(k-1)*‖iteratedFDeriv ℝ k (a l ∘ round4OriginalObserver atlas param idx) z‖ ≤ T idx l k)
    (hphase : ∀ idx l, ContDiffOn ℝ ∞ (phase l ∘ round4OriginalObserver atlas param idx) (Obs idx l))
    (hphib : ∀ idx l co s k, k ≤ j → ∀ z : X,
      parameterTensorModelEquiv (m+1) d z ∈ Samples idx → round4OriginalObserver atlas param idx z ∈ K l →
      ell^k*‖iteratedFDeriv ℝ k (fun w : X => fderiv ℝ
        (fun x => phase l (round4OriginalObserver atlas param idx (w.1,x))) w.2
        (round4OriginalTensorDirections co s)) z‖ ≤ Mp)
    (multiplicity : ℕ)
    (hmultiplicity : ∀ idx z, parameterTensorModelEquiv (m+1) d z ∈ Samples idx →
      (Finset.univ.filter (fun l => round4OriginalObserver atlas param idx z ∈ K l)).card ≤ multiplicity)
    (C : ℝ) (hC : 0 ≤ C)
    (hcost : ∀ idx l (co : Fin ((m+1)*(m+1))),
      let CR := round4ObservationJetCost (T idx l) (j+1) * round4PrescribedAmplitudeJetCost m N n length (j+1) false (weight l) Mg (Bchi l) (Bnu l)
      let CQ := round4ObservationJetCost (T idx l) (j+1) * round4PrescribedAmplitudeJetCost m N n length (j+1) true (weight l) Mg (Bchi l) (Bnu l)
      let Kc := ∑ t : Bool × Fin N, round4CompleteCoefficientJetCost j (round4OriginalTensorDirections co t.1) t.2 CR CQ Mp
      2^j*‖incrementsMeanBilinear (Λ:=Unit) (N:=N) false true‖*Kc^2 ≤ C) :
    let vf := fun l => actualProbeNormalAmplitude F (c l) (chi l) (nu l) delta tau (weight l)
    let mean := fun u => round4PrescribedNativeMean label F hF c vf phase tau length a u
    ∀ u v,
      (∀ idx, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates atlas param
        (fun b x => mean u b x-mean v b x) idx)
        ((parameterTensorModelEquiv (m+1) d).symm ⁻¹' Omega idx)) ∧
      paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates atlas param
        (fun b x => mean u b x-mean v b x)) (incrementsOriginalDifferentiation atlas param) Samples ≠ ⊤ ∧
      (paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates atlas param
        (fun b x => mean u b x-mean v b x)) (incrementsOriginalDifferentiation atlas param) Samples).toReal ≤
        ((j+1)*linearModelFactor (parameterTensorModelEquiv (m+1) d).symm j*(multiplicity:ℝ)*C)*
          delta^2*(‖u‖+‖v‖)*‖u-v‖ := by
  intro vf mean u v
  have hell : 0 < ell := htau.trans_le htaul
  let R := fun w l => round4PrescribedGlobalAmplitude false label l F hF (c l) (vf l) tau length (a l) w
  let Q := fun w l => round4PrescribedGlobalAmplitude true label l F hF (c l) (vf l) tau length (a l) w
  let coeff := fun w idx z co => round4OriginalObservedMeanCoefficient atlas param phase tau (R w) (Q w) idx z co
  have hkappa (idx) : ContinuousOn (round4OriginalObserver atlas param idx) (Omega idx) :=
    ((param idx.2).continuousOn_symm.comp continuousOn_fst (fun z hz => (hOmegaSub idx hz).1)).prodMk
      ((atlas.chart idx.1).continuousOn_symm.comp continuousOn_snd (fun z hz => (hOmegaSub idx hz).2))
  have hper (idx) (co : Fin ((m+1)*(m+1))) :
      ContDiffOn ℝ ∞ (fun z => coeff u idx z co-coeff v idx z co) (Omega idx) ∧
      ∀ k ≤ j, ∀ z : X, parameterTensorModelEquiv (m+1) d z ∈ Samples idx →
        ell^k*‖iteratedFDeriv ℝ k (fun w => coeff u idx w co-coeff v idx w co) z‖ ≤
          (multiplicity:ℝ)*C*delta^2*(‖u‖+‖v‖)*‖u-v‖ := by
    have hh := round4_prescribed_global_mean_difference_active_jets label F hF c chi nu phase a W K hW
      hK hKsource hchart hinput n length j horder Slocal hSloc hA hB hG hJ hT hBR hchi hnu
      tau ell delta Mg Mp weight Bchi Bnu htau htaul hell1 hMg hdelta hMp hBchi hBnu
      hAb hBb hGb hJb hTb hBRb hchib hnub (round4OriginalObserver atlas param idx) (Omega idx)
      ((parameterTensorModelEquiv (m+1) d) ⁻¹' Samples idx) (hOmega idx) (hSamples idx)
      (hkappa idx) (hmap idx) (Obs idx) (hObs idx) (hactive idx) (hsource idx) (htransition idx)
      (hsample idx) (T idx) (hTprof idx) (htransitionb idx) (round4OriginalTensorDirections co)
      (hphase idx) (fun l s k hk z hz hm => hphib idx l co s k hk z hz hm)
      multiplicity (hmultiplicity idx) C hC (fun l => hcost idx l co) u v
    exact hh
  have hvf (l) : ContDiffOn ℝ ∞ (fun z : X => (vf l z.1 z.2 : V)) (a l).target :=
    ((hchi l).smul (hnu l)).const_smul (-(delta*tau)/(weight l)^2)
  have hinputvf (l) : ∀ z ∈ (a l).target,
      z ∈ tsupport (fun w : X => (vf l w.1 w.2 : V)) → (a l).symm z ∈ K l := by
    intro z hz hs
    exact hinput l z hz (((tsupport_smul_subset_right _ _).trans (tsupport_smul_subset_left _ _)) hs)
  have heq (idx) (y) (hy : (parameterTensorModelEquiv (m+1) d).symm y ∈ Omega idx) :
      incrementsOriginalTensorCoordinates atlas param (fun b x => mean u b x-mean v b x) idx y =
        fun co => (coeff u idx ((parameterTensorModelEquiv (m+1) d).symm y) co-
          coeff v idx ((parameterTensorModelEquiv (m+1) d).symm y) co).re := by
    have hyO : y ∈ incrementsOriginalDifferentiation atlas param idx :=
      ⟨(hOmegaSub idx hy).2,(hOmegaSub idx hy).1⟩
    have hyW : incrementsOriginalJointPoint atlas param idx y ∈ W := hmap idx hy
    have hb (w : Pspace) := round4_prescribed_original_mean_coordinates label F hF c vf phase tau length a W K hW
      hK hKsource hchart hA hB hG hJ hT hBR hvf hinputvf hphaseGlobal atlas param hAtlas w idx y hyO hyW
    funext co
    change incrementsOriginalTensorCoordinates atlas param (mean u) idx y co-
      incrementsOriginalTensorCoordinates atlas param (mean v) idx y co = _
    rw [congrFun (hb u) co,congrFun (hb v) co,Complex.sub_re]
  let Budget := (multiplicity:ℝ)*C*delta^2*(‖u‖+‖v‖)*‖u-v‖
  have hout := round3Parameter_original_tensor_norm_of_complex_germs atlas param
    (fun b x => mean u b x-mean v b x) Samples Omega hOmega hOmegaSub hSamples
    (fun idx z co => coeff u idx z co-coeff v idx z co) (fun idx co => (hper idx co).1)
    heq j ell Budget hell hell1 (by dsimp only [Budget]; positivity)
    (fun idx co k hk z hz => (hper idx co).2 k hk z hz)
  exact ⟨hout.1,hout.2.1,hout.2.2.trans_eq (by dsimp only [Budget]; ring)⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_prescribed_original_mean_difference_norm
