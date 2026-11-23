module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocInstSt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocKvacA
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoC
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoD
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoF
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AnnihilationOperatorDoubledHermitianSpaceDecompStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AnnihilationOperatorSchroedingerFunctionsDoubledStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanParametersAddCharUniqueStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledPairThetaFunctionEqZeroOfSchrodingerEqZerStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardCartanInvolutionCommuteCompactStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumDoubledOfSchrodingerFormulasStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPolynomialFockThetaVectorWeilOperatorCartan
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerFunctionLinearThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerThetaEqSchwartzBruhatStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchroedingerFunctionFockVectorPolynomialGaussian
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ShiftedAdditiveCharacterArchimedeanParameters
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoA
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoB
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoE
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoI
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocKvacB

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn MvPolynomial
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.RhoH

variable {D : D7} {n : ℕ}




theorem const_of_annS {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hfr : IsTauFrame V τ s ε fr) (hM : ∀ τ, (gramAt D V τ * s τ).IsHermitian) (l : D.what₂.Tau → ℝ)
    (Q : PX V.rank n) (h : ∀ X, annS V l s θ τ X (tens θ τ fr (fP (cLoc l τ) Q) (psi0 θ V n l s τ)) = 0) :
    Q = C (evX Q 0) := by
  have hk : ∀ u W : Matrix (Fin V.rank) (Fin n) ℂ, ∑ k, ptX W k * eval (ptX u) (pderiv k Q) = 0 := by
    intro u W
    have e := congrFun (h (fr * W)) (xL θ τ (fr * u))
    rw [annS_tens hθ hfr hM l] at e
    have hinv : ∀ v : Matrix (Fin V.rank) (Fin n) ℂ, fr⁻¹ * (fr * v) = v := fun v => by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hfr.1, Matrix.one_mul]
    have hc : compAt θ τ (xL θ τ (fr * u)) = fr * u := by
      have := congrFun (compAt_xL hθ τ (fr * u)) τ
      simpa [dirAt_self] using this
    have hp : psi0 θ V n l s τ (xL θ τ (fr * u)) = 1 := by
      unfold psi0
      rw [compAt_xL hθ, gAway_dirAt, finPart_xL hθ]
      simp only [one_mul]
      exact gaussian_at_zero_eq_one D V.rank n
    rw [hc, hinv, hinv, hp, mul_one] at e
    exact (mul_eq_zero.1 e).resolve_right (gs_ne_zero _ _)
  have hconst : ∀ u : Matrix (Fin V.rank) (Fin n) ℂ, evX Q u = evX Q 0 := by
    intro u
    let F : ℝ → ℂ := fun t => eval (ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + (t : ℂ) • ptX u) Q
    have hF : ∀ t, HasDerivAt F 0 t := by
      intro t
      have hd := GlobalTheory.FockAnnKill.hasDerivAt_eval_line Q (ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ)) (ptX u) t
      refine hd.congr_deriv ?_
      have e2 : ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + (t : ℂ) • ptX u = ptX ((0 : Matrix (Fin V.rank) (Fin n) ℂ) + (t : ℂ) • u) :=
        (ptX_add_smul _ _ t).symm
      rw [e2]
      exact hk _ u
    have hdiff : Differentiable ℝ F := fun t => (hF t).differentiableAt
    have hc := is_const_of_deriv_eq_zero hdiff (fun t => (hF t).deriv) 1 0
    have e1 : F 1 = evX Q u := by
      show eval (ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + ((1 : ℝ) : ℂ) • ptX u) Q = eval (ptX u) Q
      rw [Complex.ofReal_one, one_smul]
      have e3 : ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + ptX u = ptX u := by
        funext k
        obtain ⟨a, i, b⟩ := k
        cases b <;> simp [ptX]
      rw [e3]
    have e0 : F 0 = evX Q 0 := by
      show eval (ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + ((0 : ℝ) : ℂ) • ptX u) Q = eval (ptX 0) Q
      rw [Complex.ofReal_zero, zero_smul, add_zero]
    rw [← e1, ← e0, hc]
  apply sub_eq_zero.1
  apply evX_eq_zero
  intro u
  show eval _ (Q - C (evX Q 0)) = 0
  rw [map_sub, eval_C]
  exact sub_eq_zero.2 (hconst u)

end PositivityTheory.Rg.Sw.Glob.RhoH
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocKvacC

section

@[expose] public section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace PositivityTheory.Rg.Sw.Glob.RhoH




theorem annS_stable : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ →
    ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ →
    ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 →
    ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω → ∀ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l →
    ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) →
    ∀ (τ : D.what₂.Tau) (Φ : schwartzA θ V.rank n), (∀ X, annS V l s θ τ X Φ.1 = 0) →
    ∀ k ∈ K D n, ∀ X, annS V l s θ τ X (ω k Φ).1 = 0 := by
  intro D n V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω l hl s hs τ Φ hann k hk X
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hstd, hsk, hlam, hψeq, hchart, hdat, htr⟩ :=
    GlobalTheory.T.exists_weilDatum_doubled_of_schrodingerFormulas D A V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω
  obtain ⟨lam', hlam', -, l', hl', habs⟩ := GlobalTheory.StdUnn.shift_char_realPar D ψ₀ hstd θ hθ μ' hsk
  have hll : lam' = lam := (algebraMap D.host.F D.host.E).injective (hlam'.trans hlam.symm)
  subst hll
  have hl'' : HasRealPar ψ θ l' := hψeq ▸ hl'
  have hleq : l = l' := GlobalTheory.T.archimedean_parameters_addChar_unique D ψ θ hθ l l' hl hl''
  subst hleq
  obtain ⟨hschS, hsurj, -⟩ := GlobalTheory.T.schrodingerTheta_eq_schwartzBruhat D ψ₀ hstd θ hθ A V μ 𝓕 hμ
  obtain ⟨f, hf, hfΦ⟩ := hsurj Φ.1 Φ.2
  obtain ⟨s', hstd', hcomm⟩ := GlobalTheory.T.exists_standardCartanInvolution_commute_compact D A μ' hsk κ hchart θ hθ

  have hkill1 : ∀ Z : Matrix (Fin V.rank) (Fin A.rank) ℂ,
      annih (heisO ψ₀ (dblSp A) V) θ τ (cplxO (s' τ) (s τ)) (Z * (dblDec A).qX.map (tauE D τ)) f = 0 := by
    intro Z
    apply GlobalTheory.T.doubledPairThetaFunction_eq_zero_of_schrodinger_eq_zero D ψ₀ hstd A V μ 𝓕 hμ _ (GlobalTheory.StdUnn.isThetaFunO_annih_of_std (A := A) (B := V) (ν := μ) (𝓨 := 𝓕) hstd hθ hμ τ _ _ hf)
    rw [GlobalTheory.T.annihilationOperator_schroedingerFunctions_doubledPair D ψ₀ hstd θ hθ A V μ 𝓕 hμ μ' hsk s' s hstd' hs l habs f hf τ Z, hfΦ]
    exact hann Z
  have hkill : ∀ Y : Matrix (Fin V.rank) (Fin (dblSp A).rank) ℂ,
      annih (heisO ψ₀ (dblSp A) V) θ τ (cplxO (s' τ) (s τ)) Y f = 0 := by
    intro Y
    obtain ⟨Z, Z', c, hdec⟩ := GlobalTheory.T.annihilationOperator_doubledHermitianSpace_decomp D ψ₀ hstd θ hθ A V μ' hsk s' s hstd' hs τ Y
    rw [hdec f hf, hkill1, hkill1, smul_zero, add_zero]

  have hkk : κ (κ.symm k) ∈ K D A.rank := by
    rw [show κ (κ.symm k) = k from κ.apply_symm_apply k]
    exact hk
  have hS : ∀ τ', s' τ' * compAt θ τ' (Formalism.L2.Theta.mt (dblSp A) (κ.symm k)) =
      compAt θ τ' (Formalism.L2.Theta.mt (dblSp A) (κ.symm k)) * s' τ' := fun τ' => (hcomm (κ.symm k) hkk τ').symm
  have hm1 : ∀ τ', compAt θ τ' (Formalism.L2.Theta.mt V 1) = 1 := by
    intro τ'
    simp [Formalism.L2.Theta.mt, compAt, Matrix.map_one]
  have hT : ∀ τ', s τ' * compAt θ τ' (Formalism.L2.Theta.mt V 1) = compAt θ τ' (Formalism.L2.Theta.mt V 1) * s τ' := by
    intro τ'
    rw [hm1, Matrix.mul_one, Matrix.one_mul]
  let X' : Matrix (Fin V.rank) (Fin A.rank) ℂ := X
  set Y0 : Matrix (Fin V.rank) (Fin (dblSp A).rank) ℂ :=
    (X' * (dblDec A).qX.map (tauE D τ)) * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) (κ.symm k)) with hY0
  have hmove := (GlobalTheory.FockMove.om_foldr hdat hθ (κ.symm k) 1 hS hT hf [(τ, Y0)]).2
  simp only [List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil] at hmove
  rw [hkill Y0, map_zero, hm1, Matrix.one_mul, hY0, Matrix.mul_assoc,
    GlobalTheory.WeilVacMove.compAt_mt_mul_inv, Matrix.mul_one] at hmove

  have htk := htr (κ.symm k) f hf Φ hfΦ.symm
  rw [show κ (κ.symm k) = k from κ.apply_symm_apply k] at htk
  have hth' : IsThetaFunO ψ₀ (dblSp A) V (omh (κ.symm k, 1) f) := hdat.om_pres _ f hf
  have e := GlobalTheory.T.annihilationOperator_schroedingerFunctions_doubledPair D ψ₀ hstd θ hθ A V μ 𝓕 hμ μ' hsk s' s hstd' hs l habs _ hth' τ X'
  rw [← hmove] at e
  have hs0 : sch ψ₀ A V μ 𝓕 (0 : WO (dblSp A) V → ℂ) = 0 := by
    have := (GlobalTheory.StdUnn.sch_linear D ψ₀ hstd A V μ 𝓕 hμ f f hf hf 0).2.2.2
    rw [zero_smul, zero_smul] at this
    exact this
  rw [hs0] at e
  show annS V l s θ τ X ((ω k) Φ).1 = 0
  rw [show ((ω k) Φ).1 = sch ψ₀ A V μ 𝓕 (omh (κ.symm k, 1) f) from htk]
  exact e.symm

end PositivityTheory.Rg.Sw.Glob.RhoH
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocKvac

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn MvPolynomial
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob




open RhoH in
theorem lIkvac : LIkvac := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL e hvac k hk
  classical
  obtain ⟨𝓕, hμ⟩ := hC.hμ
  have hΨ0m : psi0 θ V n l s τ ∈ awayA θ V n l s τ := unitaryFinitePointsToGLFiniteAdeles_isUnitary θ V l s τ
  have hl0 : ∀ τ, l τ ≠ 0 := l_ne_zero D n V ψ hC.hψ χ hC.hχ hC.hη θ hC.hθ μ 𝓕 hμ ω hC.hω l hC.hl
  have hmem : ∀ P : PX V.rank n, tens θ τ fr (fP (cLoc l τ) P) (psi0 θ V n l s τ) ∈ schwartzA θ V.rank n ∧
      tens θ τ fr (fP (cLoc l τ) P) (psi0 θ V n l s τ) ∈ fockA θ V n l s :=
    fun P => hT D n V θ l s τ ε fr hC.hθ hl0 hC.hs hC.hfr _ hΨ0m P
  have hM : ∀ τ, (gramAt D V τ * s τ).IsHermitian := fun τ => (hC.hs τ).2.2.1

  have hann1 : ∀ X, annS V l s θ τ X (phiS θ τ fr (cLoc l τ) (psi0 θ V n l s τ) 1).1 = 0 := by
    intro X
    rw [phiS_val (hmem 1).1]
    funext x
    rw [annS_tens hC.hθ hC.hfr hM l]
    simp
  have hann2 := annS_stable D n V ψ hC.hψ χ hC.hχ hC.hη θ hC.hθ μ 𝓕 hμ ω hC.hω l hC.hl s hC.hs τ _ hann1 (ι k)
    (iota_mem_K hC.hθ hC.hι k hk)
  rw [hL k _ hΨ0m 1] at hann2

  have hΦ : (phiS θ τ fr (cLoc l τ) (psi0 θ V n l s τ) 1).1 ∈ fockA θ V n l s := by
    rw [phiS_val (hmem 1).1]
    exact (hmem 1).2
  have hst := fock_stable D n V ψ hC.hψ χ hC.hχ hC.hη θ hC.hθ μ 𝓕 hμ ω hC.hω l hC.hl s hC.hs _ hΦ (ι k)
    (iota_mem_K hC.hθ hC.hι k hk)
  rw [hL k _ hΨ0m 1] at hst
  obtain ⟨Q, hQ⟩ := tens_slice hC.hθ hC.hfr l _ hst
  rw [hQ] at hann2
  have hQc := const_of_annS hC.hθ hC.hfr hM l Q hann2
  set a := evX Q 0 with ha
  have hL1 : L k (fP (cLoc l τ) 1) = a • fP (cLoc l τ) 1 := by
    rw [hQ, hQc]
    funext u
    simp [fP, evX]

  have hv := hvac k
  unfold sLd at hv
  rw [hL1] at hv
  have hg0 : gs (cLoc l τ) (0 : Fin V.rank → Fin n → ℂ) = 1 := by
    simp [gs]
  have hf0 : fP (cLoc l τ) (1 : PX V.rank n) 0 = 1 := by
    simp [fP, evX, hg0]
  simp only [Pi.smul_apply, smul_eq_mul, hf0, mul_one] at hv
  rw [hL1, hv]

end PositivityTheory.Rg.Sw.Glob
end
end
end
