module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
public import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompAtMtMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CplxOfFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdeleAt
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermCColMulVec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HxOfIsONFr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiHalfSymplecticOrthonormalFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqZeroOfReal
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesTestFunctionHolomorphicWeight
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfIsONFr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaReadingLinearInjectiveAtOrthonormalFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumCharacterPositiveDefiniteSourceStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockVacAtOfReads

section

@[expose] public section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.FockVac

theorem hasDerivAt_translate {n g : ℕ} (c : Fin g → ℝ) (H : (Fin g → ℂ) → (Fin g → ℂ) → ℂ)
    (hH : ∀ z w, H z w = ∑ j, (c j : ℂ) * z j * conj (w j)) (F : (Fin n → Fin g → ℂ) → ℂ) (hF : Differentiable ℂ F)
    (Z A : Fin n → Fin g → ℂ) :
    HasDerivAt (fun t : ℝ => cexp (Real.pi * I * ((∑ b, (H (Z b) (((t : ℂ) • A) b)).im : ℝ) : ℂ)) *
      (cexp (-(Real.pi / 2 : ℂ) * ∑ b, H ((Z + (t : ℂ) • A) b) ((Z + (t : ℂ) • A) b)) * F (Z + (t : ℂ) • A)))
      (cexp (-(Real.pi / 2 : ℂ) * ∑ b, H (Z b) (Z b)) *
        (-(Real.pi * ∑ b, H (A b) (Z b)) * F Z + fderiv ℂ F Z A)) 0 := by
  have hc : ∀ z w, conj (H z w) = H w z := fun z w => by

    simp only [hH, map_sum, map_mul, conj_ofReal, conj_conj]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have e : (fun t : ℝ => cexp (Real.pi * I * ((∑ b, (H (Z b) (((t : ℂ) • A) b)).im : ℝ) : ℂ)) *
      (cexp (-(Real.pi / 2 : ℂ) * ∑ b, H ((Z + (t : ℂ) • A) b) ((Z + (t : ℂ) • A) b)) * F (Z + (t : ℂ) • A))) =
      fun t : ℝ => (fun u : ℂ => cexp (-(Real.pi / 2 : ℂ) * ∑ b, H (Z b) (Z b) + (-(Real.pi * ∑ b, H (A b) (Z b)) * u +
        -(Real.pi / 2 : ℂ) * (∑ b, H (A b) (A b)) * u ^ 2)) * F (Z + u • A)) t := by
    funext t
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    have h1 : ∀ b, I * ((H (Z b) (((t : ℂ) • A) b)).im : ℂ) = t * (H (Z b) (A b) - H (A b) (Z b)) / 2 := fun b => by
      have h2 : H (Z b) (((t : ℂ) • A) b) = t * H (Z b) (A b) := by
        simp only [hH, Pi.smul_apply, smul_eq_mul, map_mul, conj_ofReal, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      rw [h2, ← hc (Z b) (A b), Complex.sub_conj, Complex.im_ofReal_mul]
      push_cast
      ring
    have h3 : ∀ b, H ((Z + (t : ℂ) • A) b) ((Z + (t : ℂ) • A) b) =
        H (Z b) (Z b) + t * H (Z b) (A b) + t * H (A b) (Z b) + t ^ 2 * H (A b) (A b) := fun b => by
      simp only [hH, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_add (f := _), conj_ofReal, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [Complex.ofReal_sum, mul_assoc, Finset.mul_sum]
    simp only [h1, h3, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, Finset.sum_sub_distrib]
    ring
  rw [e]
  refine HasDerivAt.comp_ofReal (e := fun u : ℂ => cexp (-(Real.pi / 2 : ℂ) * ∑ b, H (Z b) (Z b) +
    (-(Real.pi * ∑ b, H (A b) (Z b)) * u + -(Real.pi / 2 : ℂ) * (∑ b, H (A b) (A b)) * u ^ 2)) * F (Z + u • A)) ?_
  rw [Complex.ofReal_zero]
  have h1 : HasDerivAt (fun u : ℂ => Z + u • A) A 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const A).const_add Z
  have h2 : HasDerivAt (fun u : ℂ => F (Z + u • A)) (fderiv ℂ F Z A) 0 := by
    have := (hF (Z + (0 : ℂ) • A)).hasFDerivAt.comp_hasDerivAt (0 : ℂ) h1
    rwa [zero_smul, add_zero] at this
  have h3 := ((((hasDerivAt_id (0 : ℂ)).const_mul (-(Real.pi * ∑ b, H (A b) (Z b)))).fun_add
    ((hasDerivAt_pow 2 (0 : ℂ)).const_mul (-(Real.pi / 2 : ℂ) * (∑ b, H (A b) (A b))))).const_add
      (-(Real.pi / 2 : ℂ) * ∑ b, H (Z b) (Z b))).cexp.fun_mul h2
  refine h3.congr_deriv ?_
  simp only [id, zero_smul, add_zero, mul_zero, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Nat.add_one_sub_one, pow_one]
  ring

theorem isFockVacAt_of_reads : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ (x : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsONFr X x → IsInvOf W hr X x s → ∀ (f : WO V W → ℂ) (φ : TF V.rank g), IsThetaFunO ψ V W f → Reads θ V W hr X bas idx f φ x → ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO 1 (s τ)) f := by
  intro D ψ θ V W r g hr X bas idx hψ hθ hV hev hm hs x s hx0 hinv f φ hf hR τ z
  obtain ⟨hd, -, hH⟩ := hx_of_isONFr _ r g V.rank X bas idx hs hev x hx0
  obtain ⟨-, hadd, hline, -⟩ := RealCoord.zOf_coordinates D ψ θ V W r g hr X bas idx hψ hθ hV hev hm hs x
  have hJ := (GlobalTheory.FrameCplx.cplx_of_frame D ψ θ V W r g hr X bas idx hψ hθ hV hev hm hs x s hx0 hinv).2.2 τ z
  have hF := GlobalTheory.SW.ThetaHol.differentiable_thA idx hs hR.1 hd
  refine GlobalTheory.TwistFactorCompare.theta_eq_zero_of_real (WeilVacMove.isTheta_add (WeilVacMove.isTheta_dRho hψ hθ τ z hf)
    (WeilVacMove.isTheta_smul I (WeilVacMove.isTheta_dRho hψ hθ τ _ hf))) fun w hw => ?_
  have hw' : w.map (finPart D) = 0 := hw
  have key : ∀ u, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ u f w =
      cexp (-(Real.pi / 2 : ℂ) * ∑ b, hx X bas idx x (zOf θ V W hr X idx x w b) (zOf θ V W hr X idx x w b)) *
        (-(Real.pi * ∑ b, hx X bas idx x (zOf θ V W hr X idx x (lineAt θ τ u 1) b) (zOf θ V W hr X idx x w b)) *
          thA X bas idx φ x (zOf θ V W hr X idx x w) +
          fderiv ℂ (thA X bas idx φ x) (zOf θ V W hr X idx x w) (zOf θ V W hr X idx x (lineAt θ τ u 1))) := fun u => by
    rw [← (hasDerivAt_translate _ _ hH _ hF _ _).deriv]
    unfold Formalism.IndefR.Datum.dRho
    congr 1
    funext t
    have h0 : (w + lineAt θ τ u t).map (finPart D) = 0 := by
      ext i j
      have h1 := congrFun (congrFun hw' i) j
      have h2 := congrFun (congrFun ((WeilVacMove.isLineAt_lineAt hθ τ u).2.1 t) i) j
      simp only [Matrix.map_apply, Matrix.zero_apply] at h1 h2
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.zero_apply, map_add, h1, h2, add_zero]
    rw [heisO, GlobalTheory.AdThSympl.psi_symplOH_eq_of_isONFr D ψ θ V W r g hr X bas idx hψ hθ hV hev hm hs x hx0 w _ hw', hR.2 _ h0, hadd, hline]
  have hI : ∀ a b : Fin g → ℂ, hx X bas idx x (I • a) b = I * hx X bas idx x a b := fun a b => by
    simp only [hH, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [annih, Pi.add_apply, Pi.smul_apply, key, key, hJ, map_smul]
  simp only [Pi.smul_apply, hI, ← Finset.mul_sum, smul_eq_mul]
  linear_combination (cexp (-(Real.pi / 2 : ℂ) * ∑ b, hx X bas idx x (zOf θ V W hr X idx x w b) (zOf θ V W hr X idx x w b)) *
        (-(Real.pi * ∑ b, hx X bas idx x (zOf θ V W hr X idx x (lineAt θ τ z 1) b) (zOf θ V W hr X idx x w b)) *
          thA X bas idx φ x (zOf θ V W hr X idx x w) +
          fderiv ℂ (thA X bas idx φ x) (zOf θ V W hr X idx x w) (zOf θ V W hr X idx x (lineAt θ τ z 1)))) * I_mul_I

end GlobalTheory.AdTh.FockVac
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumCompactVacuumReadsDetCharacter

section

@[expose] public section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.RealCompact

theorem realM_tauE {D : D7} (θ : InfFam D) {m n : ℕ} (w : Mx D m n) (ρ : D.what₂.Tau) :
    realM θ w (tauE D ρ) = compAt θ ρ w := by
  have h : ∃ ρ', tauE D ρ = tauE D ρ' := ⟨ρ, rfl⟩
  rw [realM, dite_eq_left h, ← GlobalTheory.SmoothForms.RealPts.tauE_injective D h.choose_spec]

theorem mat_frMove {D : D7} (θ : InfFam D) (W : HSp D) (X : Data D.host.E W.rank) (k : GA D W)
    (x : Frame X.Ψ W.rank) (ρ : D.what₂.Tau) (τ : X.Ψ) (h : τ.1 = tauE D ρ) :
    mat (frMove θ W rfl X k x) τ = compAt θ ρ (Formalism.L2.Theta.mt W k) * mat x τ := by
  rw [← realM_tauE, ← h]
  rfl

theorem isONFr_frMove {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) (X : Data D.host.E W.rank)
    (hX : IsMod W rfl X) (k : GA D W) (x : Frame X.Ψ W.rank) (hx : IsONFr X x) :
    IsONFr X (frMove θ W rfl X k x) := by
  intro τ
  obtain ⟨ρ, hρ⟩ := (hX.psi τ.1).1 τ.2
  have hu : (compAt θ ρ (Formalism.L2.Theta.mt W k))ᴴ * gramAt D W ρ * compAt θ ρ (Formalism.L2.Theta.mt W k) = gramAt D W ρ :=
    GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ W k ρ
  have hG : X.Gm.map τ.1 = -(gramAt D W ρ)ᵀ := by
    rw [hX.model.1, hρ]
    ext a b
    exact map_neg (tauE D ρ) _
  have e : ∀ y : Matrix (Fin W.rank) (Fin W.rank) ℂ, FD.gram τ.1 X.Gm y = -(yᴴ * gramAt D W ρ * y)ᵀ := by
    intro y
    have e0 : FD.gram τ.1 X.Gm y = yᵀ * (X.Gm.map τ.1 * yᴴᵀ) := by
      ext a b
      simp only [FD.gram, hermC, FD.col, of_apply, Matrix.mul_apply, transpose_apply, map_apply, Finset.mul_sum, mul_assoc,
        conjTranspose_apply, RCLike.star_def]
    rw [e0, hG, transpose_mul, transpose_mul, Matrix.neg_mul, Matrix.mul_neg]
  rw [mat_frMove θ W X k x ρ τ hρ, ← hx τ, e, e, conjTranspose_mul]
  congr 2
  conv_rhs => rw [← hu]
  simp only [Matrix.mul_assoc]

theorem om_compact_reads : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsPair ψ θ V W χV χW om → ∀ mu : GA D W → ℂ, Formalism.L2.Pj.MuVal W χV mu → ∀ (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsMod W hr X → IsSympl X bas → ∀ (x : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsONFr X x → IsInvOf W hr X x s → ∀ (f : WO V W → ℂ) (φ : TF V.rank g), IsThetaFunO ψ V W f → Reads θ V W hr X bas idx f φ x → ∀ k ∈ GinfC W, (∀ τ, s τ * compAt θ τ (Formalism.L2.Theta.mt W k) = compAt θ τ (Formalism.L2.Theta.mt W k) * s τ) → Reads θ V W hr X bas idx (om (1, k) f) (mu k • φ) (frMove θ W hr X k x) := by
  intro D ψ θ V W χV χW om hP mu hmu r g hr X bas idx hX hS x s hx hs f φ hf hR k hk hks
  subst hr
  have hstd := hP.weil.std
  obtain ⟨cW, cV, -⟩ := GlobalTheory.FrameCplx.cplx_of_frame D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS x s
    hx hs
  have hvac := GlobalTheory.AdTh.FockVac.isFockVacAt_of_reads D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS x s
    hx hs f φ hf hR
  choose a ha using hP.expV
  choose b hb using hP.expW
  obtain ⟨n, hn⟩ := hP.even
  choose p hp hd using fun τ => GlobalTheory.VacuumCharacter.detPlus_one (n := 0) (s τ) (cW τ).1
  have hom := GlobalTheory.T.vacuum_character_positive_definite_source D ψ θ V W χV χW om hP.weil hP.inf hP.sigV hP.sigW s cV cW _ _ ha hb
    (fun τ => a τ + n) (fun τ => a τ - n) (fun τ => -(p τ + b τ))
    (fun τ => by rw [hn]; push_cast; ring) (fun τ => by rw [hn]; push_cast; ring)
    (fun τ => by rw [hp]; push_cast; ring) f hf hvac 1 (one_mem _) k hk hks
  have hx' := isONFr_frMove hP.inf W X hX k x hx
  have hs' : IsInvOf W rfl X (frMove θ W rfl X k x) s := fun ρ τ h => by
    have e1 : s ρ * mat x τ = -(mat x τ * sgnM X) := hs ρ τ h
    show s ρ * _ = _
    rw [mat_frMove θ W X k x ρ τ h, ← Matrix.mul_assoc, hks, Matrix.mul_assoc, e1, Matrix.mul_neg, Matrix.mul_assoc]
  have h2 := GlobalTheory.AdTh.reads_two_frames D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS x _ s hx hx' hs hs'
    (fun ρ => compAt θ ρ (Formalism.L2.Theta.mt W k)) (fun ρ τ h => mat_frMove θ W X k x ρ τ h) f φ hR
  obtain ⟨y, hy, hyv⟩ := GlobalTheory.VacuumCharacter.exists_root hP.inf W
    (fun τ => (GlobalTheory.SmoothForms.RealPts.gramAt_unit W τ).ne_zero) k hk
  have hmk : mu k = ∏ τ, (compAt θ τ (Formalism.L2.Theta.mt W k)).det ^ a τ := by rw [hmu.2 k y hy, hyv χV a ha]
  have h3 := fun c : ℂ => (GlobalTheory.AdTh.reads_linear_injective D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS
    _ hx' _ _ _ _ h2 h2).1 c 0
  simp only [zero_smul, add_zero] at h3
  rw [hom]
  convert h3 _ using 1
  rw [smul_smul, hmk, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  have d2 := (hd τ 1 _ (hks τ)).2
  have h0 : (compAt θ τ (Formalism.L2.Theta.mt W k)).det ≠ 0 := by
    have := congrArg Matrix.det (GlobalTheory.UnitaryChar.compAt_mt_mul θ W τ k k⁻¹)
    rw [mul_inv_cancel, GlobalTheory.UnitaryChar.compAt_mt_one, det_one, det_mul] at this
    exact left_ne_zero_of_mul_eq_one this.symm
  have hn2 : V.rank / 2 = n := by omega
  rw [d2] at h0
  rw [GlobalTheory.UnitaryChar.compAt_mt_one, det_one, _root_.one_zpow, mul_one, hn2]
  conv_lhs => rw [d2]
  have hA := left_ne_zero_of_mul h0
  have hB := right_ne_zero_of_mul h0
  generalize ((1 / 2 : ℂ) • (1 + s τ) * compAt θ τ (Formalism.L2.Theta.mt W k) + (1 / 2 : ℂ) • (1 - s τ)).det = A at hA ⊢
  generalize ((1 / 2 : ℂ) • (1 - s τ) * compAt θ τ (Formalism.L2.Theta.mt W k) + (1 / 2 : ℂ) • (1 + s τ)).det = B at hB ⊢
  rw [mul_zpow, zpow_add₀ hA, zpow_sub₀ hB, zpow_natCast, zpow_natCast, div_pow]
  have := pow_ne_zero n hA
  have := pow_ne_zero n hB
  field_simp

end GlobalTheory.AdTh.RealCompact
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumCompactVacuumReadsDetCharacterStatement

section

@[expose] public section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weilDatum_compact_vacuum_reads_det_character : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsPair ψ θ V W χV χW om → ∀ mu : GA D W → ℂ, Formalism.L2.Pj.MuVal W χV mu → ∀ (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsMod W hr X → IsSympl X bas → ∀ (x : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsONFr X x → IsInvOf W hr X x s → ∀ (f : WO V W → ℂ) (φ : TF V.rank g), IsThetaFunO ψ V W f → Reads θ V W hr X bas idx f φ x → ∀ k ∈ GinfC W, (∀ τ, s τ * compAt θ τ (Formalism.L2.Theta.mt W k) = compAt θ τ (Formalism.L2.Theta.mt W k) * s τ) → Reads θ V W hr X bas idx (om (1, k) f) (mu k • φ) (frMove θ W hr X k x) := by
  first | exact @GlobalTheory.AdTh.RealCompact.om_compact_reads | exact GlobalTheory.AdTh.RealCompact.om_compact_reads | (intros; apply GlobalTheory.AdTh.RealCompact.om_compact_reads <;> assumption)
end
end
