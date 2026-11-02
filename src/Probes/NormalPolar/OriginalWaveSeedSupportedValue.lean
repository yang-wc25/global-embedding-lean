import NormalPolar.GlobalWaveResponseSupport

/-!
# The actual global value response for a supported original piece

The closed original piece carrier and actual leading value are retained. At an
active point, the source chart, phase and physical amplitude identities pull
back the proved native column. At every other point the complete global
column and the original wave value are both zero.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
  GlobalEmbedding.Continuation
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade
variable {n m N p r : ℕ} {M Ep : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "IM" => 𝓘(ℝ,EuclideanSpace ℝ (Fin n))
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

theorem globalWave_native_value_response_supported
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := IM) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (tau : ℝ) (length : ℕ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (W : Set (Ep × M)) (K : Fin r → Set (Ep × M)) (hW : IsOpen W)
    (hK : ∀ l, IsClosed (Subtype.val ⁻¹' K l : Set W)) (hKsource : ∀ l, K l ⊆ (a l).source)
    (hchart : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod IM) 𝓘(ℝ,X) ∞ (a l) (a l).source)
    (hA : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hB : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hG : ∀ l, ContDiffOn ℝ ∞ (fun z : X => freeGramRightInverse (fderiv ℝ (F z.1 ∘ c l z.1) z.2)) (a l).target)
    (hJ : ∀ l, ContDiffOn ℝ ∞ (fun z : X => (normalSpace (I := IM) (F z.1) (c l z.1 z.2)).subtypeL.comp
      (incrementsModeCoordinateJ (F z.1) (hF z.1) (c l z.1) z.2)) (a l).target)
    (hT : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeTransverseValue (F z.1) (c l z.1) z.2) (a l).target)
    (hBR : ∀ l, ContDiffOn ℝ ∞ (fun z : X => fun k : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c l z.1) z.2 0 k : V)) (a l).target)
    (hvf : ∀ l, ContDiffOn ℝ ∞ (fun z : X => (vf l z.1 z.2 : V)) (a l).target)
    (hinput : ∀ l z, z ∈ (a l).target → z ∈ tsupport (fun w : X => (vf l w.1 w.2 : V)) → (a l).symm z ∈ K l)
    (hphase : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod IM) 𝓘(ℝ,ℝ) ∞ (phase l) (W ∩ (a l).source))
    (i : Fin r) (b : Ep) (chi : X → ℝ)
    (nu : (t : Ep) → (y : D) → normalSpace (I := IM) (F t) (c i t y))
    (delta ell weight : ℝ) (psi : D → ℝ)
    (hphysical : vf i = actualProbeNormalAmplitude F (c i) chi nu delta tau weight)
    (hinverse : ∀ z ∈ (a i).target, (a i).symm z = (z.1,c i z.1 z.2))
    (hsourceW : (a i).source ⊆ W)
    (hobs : ContMDiffOn 𝓘(ℝ,D) IM ∞ (c i b) ((fun y : D => (b,y)) ⁻¹' (a i).target))
    (hphaseChart : ∀ y, (b,y) ∈ (a i).target → phase i ((a i).symm (b,y)) = weight*psi y)
    (hpsi : ContDiffOn ℝ ∞ psi ((fun y : D => (b,y)) ⁻¹' (a i).target))
    (hchi : ContDiffOn ℝ ∞ chi (a i).target)
    (hnu : ContDiffOn ℝ ∞ (fun z : X => (nu z.1 z.2 : V)) (a i).target)
    (S : Set D) (hS : ∀ y ∈ S, (b,y) ∈ (a i).target)
    (MB Mg Bchi Bnu Mpsi : ℝ)
    (hdelta : 0 ≤ delta) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (htau : 0 < tau) (htaul : tau ≤ ell) (hweight : 0 < weight)
    (hMB : 0 ≤ MB) (hMg : 0 ≤ Mg) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu)
    (hBRb : ∀ k ≤ 2+length+1, ∀ z ∈ (a i).target, ell^k*‖iteratedFDeriv ℝ k
      (fun w : X => fun d : Fin (m+1) =>
        (incrementsModeSecondForm (F w.1) (hF w.1) (c i w.1) w.2 0 d : V)) z‖ ≤ MB)
    (hchib : ∀ k ≤ 2+length+1, ∀ z ∈ (a i).target, ell^k*‖iteratedFDeriv ℝ k chi z‖ ≤ Bchi)
    (hnub : ∀ k ≤ 2+length+1, ∀ z ∈ (a i).target, ell^k*‖iteratedFDeriv ℝ k
      (fun w : X => (nu w.1 w.2 : V)) z‖ ≤ Bnu)
    (hAb : ∀ k ≤ 2+length+1, ∀ y ∈ S, ell^k*‖iteratedFDeriv ℝ k
      (incrementsModeComplexFirstOrderA (F b) (hF b) (c i b)) y‖ ≤ Mg)
    (hBb : ∀ k ≤ 2+length+1, ∀ y ∈ S, ell^k*‖iteratedFDeriv ℝ k
      (incrementsModeComplexFirstOrderB (F b) (hF b) (c i b)) y‖ ≤ Mg)
    (hGb : ∀ k ≤ 2, ∀ y ∈ S, ell^k*‖iteratedFDeriv ℝ k
      (fun y => freeGramRightInverse (fderiv ℝ (F b ∘ c i b) y)) y‖ ≤ Mg)
    (hJb : ∀ k ≤ 2, ∀ y ∈ S, ell^k*‖iteratedFDeriv ℝ k
      (fun y => (normalSpace (I := IM) (F b) (c i b y)).subtypeL.comp
        (incrementsModeCoordinateJ (F b) (hF b) (c i b) y)) y‖ ≤ Mg)
    (hTb : ∀ k ≤ 2, ∀ y ∈ S, ell^k*‖iteratedFDeriv ℝ k
      (incrementsModeTransverseValue (F b) (c i b)) y‖ ≤ Mg)
    (hpsib : ∀ k < 2, ∀ y ∈ S, ell^k*‖iteratedFDeriv ℝ (k+1) (fun y => weight*psi y) y‖ ≤ Mpsi)
    (carrier : Set M) (theta : M → ℝ) (amplitude : M → V)
    (hamplitudeZero : ∀ x, x ∉ carrier → amplitude x = 0)
    (source : OpenPartialHomeomorph M D)
    (hcarrier : carrier ⊆ source.source)
    (hcoordinate : ∀ y ∈ source.target, c i b y = source.symm y)
    (hpsiOriginal : ∀ y ∈ source.target, psi y = theta (source.symm y))
    (hamplitudeOriginal : ∀ y ∈ source.target,
      chi (b,y) • (nu b y : V) = amplitude (source.symm y))
    (hsamples : ∀ y ∈ carrier, source y ∈ S)
    (hsliceW : ∀ y, (b,y) ∈ W)
    (hactualCarrier : ∀ q ∈ K i, q.2 ∈ carrier) :
    let CV := actualRealHomogeneousConstant m N 2 length Mg
      (homogeneousSourceConstant m N (2+length+1) MB
        (probeNormalAmplitudeConstant (2+length+1) weight Bchi Bnu)) Mpsi
    ∀ (x : M) (u : ProbeParameters r) (sine : Bool),
      ‖fderiv ℝ (fun v => round4PrescribedGlobalWave label F hF c vf phase tau length a
          (probeParameterEmbedding label v) (b,x)) u (Pi.single (i,sine) 1) -
        (-(delta*tau)*(weight^2)⁻¹ * probeTrig sine (weight*theta x/tau)) • amplitude x‖ ≤
        (delta*tau)*(tau/ell)* |CV| := by
  intro CV x u sine
  by_cases hk : x ∈ carrier
  · have hxs := hcarrier hk
    have hxt := source.map_source hxs
    have hc : c i b (source x) = x := by
      rw [hcoordinate _ hxt,source.left_inv hxs]
    have hp : psi (source x) = theta x := by
      rw [hpsiOriginal _ hxt,source.left_inv hxs]
    have ha : chi (b,source x) • (nu b (source x) : V) = amplitude x := by
      rw [hamplitudeOriginal _ hxt,source.left_inv hxs]
    have hh := globalWave_native_value_principal_paired label F hF c vf phase tau length a W K hW hK hKsource hchart
      hA hB hG hJ hT hBR hvf hinput hphase i b chi nu delta ell weight psi hphysical
      hinverse hsourceW hobs hphaseChart hpsi hchi hnu S hS MB Mg Bchi Bnu Mpsi
      hdelta hell hell1 htau htaul hweight hMB hMg hBchi hBnu hBRb hchib hnub
      hAb hBb hGb hJb hTb hpsib (source x) (hsamples x hk) u sine
    change ‖fderiv ℝ (fun v => round4PrescribedGlobalWave label F hF c vf phase tau length a
        (probeParameterEmbedding label v) (b,c i b (source x))) u (Pi.single (i,sine) 1) -
      (-(delta*tau)*(weight^2)⁻¹ * probeTrig sine (weight*psi (source x)/tau)) •
        (chi (b,source x) • (nu b (source x) : V))‖ ≤ (delta*tau)*(tau/ell)*CV at hh
    rw [ha,hp,hc] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (le_abs_self CV) (by positivity))
  · have hsupport := globalWave_single_column_support label F hF c vf phase tau length a W K hW hK
      hKsource hchart hA hB hG hJ hT hBR hvf hinput hphase i sine
    have hn : (b,x) ∉ K i := fun hh => hk (hactualCarrier _ hh)
    have hgerm := globalWave_zero_germ_of_relative_tsupport W (K i) hW (hK i)
      (fun q => round4PrescribedGlobalWave label F hF c vf phase tau length a
        (Pi.single (label (i,sine)) 1) q) hsupport (b,x) (hsliceW x) hn
    have hr := globalWave_native_paired_column label F hF c vf phase tau length a W K hW hK hKsource
      hchart hA hB hG hJ hT hBR hvf hinput hphase u i sine (b,x)
    have hv : amplitude x = 0 := hamplitudeZero x hk
    rw [hr,hgerm.eq_of_nhds,hv,smul_zero,sub_zero]
    simp only [Pi.zero_apply,norm_zero]
    positivity

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.globalWave_native_value_response_supported
