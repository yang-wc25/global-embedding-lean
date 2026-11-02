import Probes.ActualSecondaryPhysicalRawCoefficients
import Probes.ActualSecondaryQuadraticConstruction
import Probes.ActualSecondaryPhysicalCoefficientSupport

/-! One actual global secondary piece is selected in one fixed host chart.
Raw original profiles supply its physical coefficients internally, and those
supply the literal negative signed quadratic hR/hI and the SAME supported
finite wave. This construction is independent of every later observer chart.
The actual phase, inverse transition, support, and both tensor slots remain.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold GlobalEmbedding.Paper
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {Ep M Tr : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  {Label Sub : Type*} [Fintype Label] [Fintype Sub]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

 theorem actual_secondary_piece_from_original_raw_profiles
    (nInput nSolve q Rsub Lprimary : ℕ) (hq : 1 ≤ q) (horder : nSolve+2+(q+2) ≤ nInput)
    (reserve Bnd Mg Kcut : ℝ) (hc : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (T Tinv : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k) :
    ∃ CH : ℝ, 0 ≤ CH ∧ ∀
      (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
      (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := Sub) F)
      (input inputbar : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
      (W : Set (Ep × M)) (primary : Label → Set (Ep × M)) (j : ℕ) (ell delta tau Delta : ℝ)
      (d : ActualSecondaryRawGeometry F hF nSolve j ell Mg W)
      (e : OpenPartialHomeomorph M D)
      (he : ContMDiffOn 𝓙 𝓘(ℝ,D) ∞ e e.source)
      (heInv : ContMDiffOn 𝓘(ℝ,D) 𝓙 ∞ e.symm e.target)
      (hhost : d.chart.source ⊆ ((OpenPartialHomeomorph.refl Ep).prod e).source)
      (nu mu : Label) (branch : Fin 4),
      let host := (OpenPartialHomeomorph.refl Ep).prod e
      let transition := host.symm.trans d.chart
      let phi := fun a t x => g.phase a (t,e.symm x)
      let P := fun a t beta x => delta •
        incrementsGlobalPrimaryExtension F hF g input (q+2) tau true a beta (t,e.symm x)
      let Q := fun a t beta x => delta •
        incrementsGlobalPrimaryExtension F hF g input (q+2) tau false a beta (t,e.symm x)
      let psi := fun y => ![g.phase nu y+g.phase mu y,g.phase nu y-g.phase mu y,
        -g.phase nu y+g.phase mu y,-g.phase nu y-g.phase mu y] branch
      ∀ (hphase : d.phase = psi) (cutoff : X → ℝ)
        (hcutoff : ContDiffOn ℝ ∞ cutoff transition.source)
        (hInv : ContDiffOn ℝ ∞ transition.symm transition.target)
        (hcutSupport : ∀ y ∈ host.target, host.symm y ∈ W →
          y ∈ tsupport cutoff →
          host.symm y ∈ incrementsGlobalRelativeSupport W (g.cutoff nu) ∩
            incrementsGlobalRelativeSupport W (g.cutoff mu) → host.symm y ∈ d.support)
        (raw : ParameterRound2GlobalMeanRawProfiles (Tr := Tr) nInput (q+2) nSolve Rsub Lprimary
          reserve Bnd Mg T F hF g input inputbar W primary e transition.source
          (transition.symm '' d.sample) tau ell Delta)
        (hcut : ∀ r ≤ nSolve, ∀ z ∈ d.sample,
          ell^r*‖iteratedFDeriv ℝ r cutoff (transition.symm z)‖ ≤ Kcut)
        (hinv : ∀ r, 1 ≤ r → r ≤ nSolve+1 → ∀ z ∈ d.sample,
          ell^(r-1)*‖iteratedFDeriv ℝ r transition.symm z‖ ≤ Tinv r),
      let H := incrementsSecondaryQuadraticForcing phi tau (fun _ _ _ _ => 1) P Q
        (fun i _ => EuclideanSpace.single i 1) nu mu branch
      let hR := actualSecondaryInverseForcing transition cutoff (fun z => actualRealTensorAssembly (H z))
      let hI := actualSecondaryInverseForcing transition cutoff (fun z => actualImaginaryTensorAssembly (H z))
      ∃ out : ActualSecondaryPhysicalPieceData F hF nSolve j ell Mg CH delta W,
        out.base.c = d.c ∧ out.base.chart = d.chart ∧ out.base.phase = psi ∧
        out.base.support = d.support ∧ out.base.sample = d.sample ∧
        out.base.hR = hR ∧ out.base.hI = hI ∧
        ∀ tau' length, out.base.wave tau' length =
          actualSecondarySupportedWave F hF d.c hR hI d.chart psi tau' length := by
  obtain ⟨MD,hMD,hcoeff⟩ := actual_original_physical_coefficient_profiles_from_raw
    (I := 𝓙) (M := M) (Ep := Ep) (Tr := Tr) (m := m) (N := N) (Λ := Label) (Β := Sub)
    nInput q nSolve Rsub Lprimary hq horder reserve Bnd Mg hc hBnd hMg T hT
  obtain ⟨CH,hCH,hconstruct⟩ := actual_secondary_quadratic_piece_from_geometry
    (m := m) (N := N) (Ep := Ep) (M := M) nSolve MD Kcut hMD hKcut Tinv hTinv
  refine ⟨CH,hCH,?_⟩
  intro F hF g input inputbar W primary j ell delta tau Delta d e he heInv hhost nu mu branch
    host transition phi P Q psi hphase cutoff hcutoff hInv hcutSupport raw hcut hinv H hR hI
  have hTarget : ∀ z ∈ transition.source, z.2 ∈ e.target := by
    intro z hz
    have hh : z ∈ host.target := (show z ∈ host.target ∧ host.symm z ∈ d.chart.source from hz).1
    exact hh.2
  have hnu := hcoeff F hF g input inputbar W primary e he heInv transition.source
    (transition.symm '' d.sample) tau ell Delta raw hTarget delta nu
  have hmu := hcoeff F hF g input inputbar W primary e he heInv transition.source
    (transition.symm '' d.sample) tau ell Delta raw hTarget delta mu
  have hSupportActual : ∀ y ∈ host.target, host.symm y ∈ W →
      y ∈ tsupport cutoff →
      y ∈ tsupport (fun z => incrementsSecondaryPhysicalCoefficient phi tau (fun _ _ _ _ => 1)
        P Q (fun i _ => EuclideanSpace.single i 1) z nu) ∩
        tsupport (fun z => incrementsSecondaryPhysicalCoefficient phi tau (fun _ _ _ _ => 1)
          P Q (fun i _ => EuclideanSpace.single i 1) z mu) → host.symm y ∈ d.support := by
    intro y hy hyW hyCut hyPair
    apply hcutSupport y hy hyW hyCut
    let O := host.target ∩ host.symm ⁻¹' W
    have hO : IsOpen O := host.symm.continuousOn.isOpen_inter_preimage host.open_target raw.prim.hW
    have hyO : y ∈ O := ⟨hy,hyW⟩
    have hTgt : ∀ z ∈ O, z.2 ∈ e.target := fun z hz => hz.1.2
    have hMap : MapsTo (fun z : X => (z.1,e.symm z.2)) O W := fun z hz => hz.2
    exact ⟨actual_original_physical_coefficient_support_on F hF g input q hq tau delta raw.htau
      W primary raw.prim e he heInv O hO hTgt hMap y hyO nu hyPair.1,
      actual_original_physical_coefficient_support_on F hF g input q hq tau delta raw.htau
        W primary raw.prim e he heInv O hO hTgt hMap y hyO mu hyPair.2⟩
  obtain ⟨out,hc0,hchart,hp,hs,hsample,hr,hi,hw⟩ := hconstruct F hF j ell Mg delta W d host hhost
    phi tau (fun _ _ _ _ => 1) P Q nu mu branch cutoff hcutoff hInv hSupportActual
    (raw.htau.trans_le raw.htaul) hnu.1 hmu.1
    (fun r hrr z hz => hnu.2.1 r hrr (transition.symm z) ⟨z,hz,rfl⟩)
    (fun r hrr z hz => hmu.2.1 r hrr (transition.symm z) ⟨z,hz,rfl⟩) hcut hinv
  refine ⟨out,hc0,hchart,hp.trans hphase,hs,hsample,hr,hi,?_⟩
  intro tau' length
  rw [hw tau' length,hphase]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_secondary_piece_from_original_raw_profiles
