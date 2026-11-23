module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GamAtOfLawsCore
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaNetDimensionAndPointCountBound
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProofStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmFamilyFunctionalsDetectLowCoefficients
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDatumSectionValueCoeffEqFourierJacobiStatement
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TraceFormIndependence
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MemFormsLowCoeffsVanishIffFourierJacobiStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TransvInOfHasPrinc
public import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPolynomialBoundRunConstantsDegreeFourStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.QuotientBoundOfKillDetectConstantRoom
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.NormNum.Parity

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmArcFunctionalVanishesLowFourierJacobi

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcKill

theorem eq_zero_of_eval_off {σ : Type} {P Q : MvPolynomial σ ℂ} (hQ : Q ≠ 0)
    (h : ∀ x, MvPolynomial.eval x Q ≠ 0 → MvPolynomial.eval x P = 0) : P = 0 := by
  have : P * Q = 0 := MvPolynomial.funext fun x => by
    rw [map_mul, map_zero]
    by_cases hx : MvPolynomial.eval x Q = 0
    · rw [hx, mul_zero]
    · rw [h x hx, zero_mul]
  exact (mul_eq_zero.1 this).resolve_right hQ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem coeff_eq_zero_of_invBl (S : Finset (ArcLt Dw →₀ ℕ)) (f : (ArcLt Dw →₀ ℕ) → ℂ)
    (h : ∀ x : ArcLt Dw → ℂ, InvBl x → ∑ mo ∈ S, f mo * ∏ v ∈ mo.support, x v ^ mo v = 0) : ∀ mo ∈ S, f mo = 0 := by
  classical
  let Q : MvPolynomial (ArcLt Dw) ℂ := ∏ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) =>
    (MvPolynomial.X (⟨τ, (i, k)⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) ℂ)).det
  have hQe : ∀ x : ArcLt Dw → ℂ, MvPolynomial.eval x Q ≠ 0 ↔ InvBl x := fun x => by
    rw [map_prod, Finset.prod_ne_zero_iff]
    refine forall_congr' fun τ => ?_
    have : (MvPolynomial.eval x).mapMatrix (Matrix.of fun i k : Fin (Dw.mult τ) =>
        (MvPolynomial.X (⟨τ, (i, k)⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) ℂ)) =
        Matrix.of fun i k : Fin (Dw.mult τ) => x ⟨τ, (i, k)⟩ := by
      ext i k : 2
      simp
    rw [RingHom.map_det, this]
    simp
  have hone : InvBl (Dw := Dw) fun v => (1 : Matrix (Fin (Dw.mult v.1)) (Fin (Dw.mult v.1)) ℂ) v.2.1 v.2.2 :=
    fun τ => (Matrix.det_one (n := Fin (Dw.mult τ)) (R := ℂ)).trans_ne one_ne_zero
  have hQ : Q ≠ 0 := fun h0 => (hQe _).2 hone (by rw [h0, map_zero])
  have hP : ∑ mo ∈ S, MvPolynomial.monomial mo (f mo) = 0 := eq_zero_of_eval_off hQ fun x hx => by

    rw [map_sum, ← h x ((hQe x).1 hx)]
    exact Finset.sum_congr rfl fun mo _ => MvPolynomial.eval_monomial
  intro mo hmo
  have := congrArg (AddMonoidAlgebra.coeff · mo) hP
  rw [MvPolynomial.coeff_sum] at this
  simpa [MvPolynomial.coeff_monomial, hmo] using this

theorem cfOf_eq_zero : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (em : K₁ →+* ℂ) (r : ℕ) (U : Unf Xo c (em.comp (algebraMap c.F K₁)) r) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Fam n' La c₁ d → GoodEmb c (em.comp (algebraMap c.F K₁)) → IsUnf U → Dom a' n → (∀ k, TransvIn (U.X k) l.M' (laU U a' n k)) → ∀ F ∈ sec Xo c a' n, (∀ k, rdU U F k ∈ (U.X k).SSgt (laU U a' n k) c₁) → cfOf d.yF d.μ d.jj F = 0 := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ _ d n' La c₁ em r U a' n hfam hgood hunf hdom htv F hF hS
  obtain ⟨⟨hover, -, hpush⟩, ⟨s⟩⟩ := hfam
  obtain ⟨k, ξ', fr, u₁, κ, hu, hiso, -, hfr, hmain⟩ := GlobalTheory.T.arcDatum_sectionValue_coeff_eq_fourierJacobi hK.laws hK.laws2 hK.ubc hK.laws5 hK.n5
    E H Dw l Xo c K₁ d em r U s.ξ s.ν₀ a' n (hK.ev E H Dw l Xo c) hgood hunf hover s.tan hpush s.rk s.ξ_ne s.beta
    hdom htv
  have hν : ∑ τ : (U.X k).Ψ, (τ.1 s.ν₀).re ≤ c₁ := by
    have h1 := TraceFormIndependence.trace_re (U.X k) s.ν₀
    have h2 := s.tr
    rw [h1, ← Finset.mul_sum] at h2
    linarith
  have h0 : ∀ x, InvBl x → ajAt d em F x = 0 := fun x hx => by
    have := hmain F hF (hS k).1.1 x hx
    rw [(hS k).2 ξ' hiso _ hν _ (hfr x hx), mul_zero] at this
    exact (mul_eq_zero.1 this).resolve_right (zpow_ne_zero _ hu)
  unfold cfOf
  by_cases hmo : d.μ ∈ (arcNum (evR Xo c F d.yF)).support
  · exact (map_eq_zero em).1 (coeff_eq_zero_of_invBl _
      (fun mo => em (((arcNum (evR Xo c F d.yF)).coeff mo).coeff d.jj)) h0 _ hmo)
  · rw [MvPolynomial.notMem_support_iff.1 hmo]
    rfl

end GlobalTheory.ArcKill
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmArcFunctionalVanishesLowFourierJacobiStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.cmArcFunctional_vanishes_low_fourierJacobi : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (em : K₁ →+* ℂ) (r : ℕ) (U : Unf Xo c (em.comp (algebraMap c.F K₁)) r) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Fam n' La c₁ d → GoodEmb c (em.comp (algebraMap c.F K₁)) → IsUnf U → Dom a' n → (∀ k, TransvIn (U.X k) l.M' (laU U a' n k)) → ∀ F ∈ sec Xo c a' n, (∀ k, rdU U F k ∈ (U.X k).SSgt (laU U a' n k) c₁) → cfOf d.yF d.μ d.jj F = 0 := by
  first | exact @GlobalTheory.ArcKill.cfOf_eq_zero | exact GlobalTheory.ArcKill.cfOf_eq_zero | (intros; apply GlobalTheory.ArcKill.cfOf_eq_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsExtendEmbedding

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

namespace GlobalTheory.ArcCM

theorem exists_extend_embedding {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K] [Algebra F K]
    (σ : F →+* ℂ) : ∃ em : K →+* ℂ, em.comp (algebraMap F K) = σ := by
  letI : Algebra F ℂ := σ.toAlgebra
  haveI : Algebra.IsAlgebraic F K := Algebra.IsAlgebraic.tower_top (K := ℚ) F
  let f : K →ₐ[F] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨f.toRingHom, RingHom.ext fun x => f.commutes x⟩

theorem killQ_of_gamAt : Known → ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ), GlobalTheory.RunIn.GamAt T → InR D j → j < D.R.m → KillQ h j ka CR Tt cc := by
  intro hK D T h j ka CR Tt cc hG hj hm K₁ _ _ _ d hd F hF
  have key : ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ →
      (∀ k, rdU (T.U j σ) F.1 k ∈ ((T.U j σ).X k).SSgt (laU (T.U j σ) (wtA ka) ka.n k) (WeightFamilies.c1 D CR Tt cc j)) →
      cfOf d.yF d.μ d.jj F.1 = 0 := by
    intro σ hσ hr
    obtain ⟨em, rfl⟩ := exists_extend_embedding (K := K₁) σ
    have hc : F.1 ∈ T.C j ka := cutR_le T.C j ka F.2
    exact GlobalTheory.T.cmArcFunctional_vanishes_low_fourierJacobi hK _ _ _ _ (T.Q.Xo j) T.Q.c K₁ d _ _ _ em _
      (Formalism.L2.PjFree.Unf.ofPj (T.U j _)) (wtA ka) ka.n hd hσ (h.unf j hj _ hσ) (dom_wtA ka)
      (GlobalTheory.TransvPrinc.transvIn_of_hasPrinc _ _ _ _ (T.Q.Xo j) T.Q.c _ _ (Formalism.L2.PjFree.Unf.ofPj (T.U j _)) (wtA ka) ka.n
        (hG j hj _ hσ) (h.chiTriv j hj _ hσ _ _ (dom_wtA ka))) F.1 hc.1 hr
  exact key T.σ₀ T.good_σ₀ ((GlobalTheory.T.mem_forms_low_coeffs_vanish_iff_fourierJacobi D T h j ka CR Tt cc hj hm F).2.1 hF)

end GlobalTheory.ArcCM
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RecursivePageLatticeBound

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

set_option autoImplicit false

namespace GlobalTheory.RunJoin




theorem qAt_run : ∃ Cq : ℝ → ℝ → ℝ, ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → j < D.R.m → LatAt (recB h.toLawsCore) j ka → QAt large₂ (recB h.toLawsCore) j ka 7 H.CK 1 4 (Cq H.CA H.CK) 4 Tn (cc D large₂ C2 A2 7 wL) := by
  obtain ⟨C₀, hC₀, hroom⟩ := GlobalTheory.T.exists_polynomial_bound_runConstants_degree_four
  refine ⟨fun a b => 1 + 3 * C₀ a 7 b + 1041, ?_⟩
  intro D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hP hjm hL hCR hO hn hlast hsz hT hc hTc
  have h3 : 3 ≤ D.R.r := le_trans (by norm_num) hP.r8
  have hcc : Real.log (Ideal.absNorm D.host.ccK) ≤ large₂.sc.L := by
    obtain ⟨Q, -, -⟩ := hP.page
    exact Q.ccK_log
  obtain ⟨hZ, hR⟩ := hroom D large₂ j ka H.CA 7 H.CK Tn (cc D large₂ C2 A2 7 wL) hP.hyp.1 hcc hj hjm h3 hCR hsz hT hc hTc
  obtain ⟨-, -, -, -, -, -, -, -, hdim, -⟩ := GlobalTheory.RunJoin.net_at_run D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hP
  have hG := GlobalTheory.RunIn.gamAt_of_lawsCore D T.toCore h.toLawsCore
  have hK := GlobalTheory.T.arithmeticCMKnownTheorems_proof
  have hpp : 1041 * Zb D large₂ ^ 3 ≤ WeightFamilies.PPv D large₂ 1041 3 * ka.size := by
    have e : WeightFamilies.PPv D large₂ 1041 3 = 1041 * Zb D large₂ ^ 3 := by
      unfold WeightFamilies.PPv
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rfl
    rw [e]
    have hZ' : (1 : ℝ) ≤ Zb D large₂ := hZ
    exact le_mul_of_one_le_right (by positivity) ka.one_le_size
  have key := GlobalTheory.ArcCM.qat_of_kill_detect hK D T.toCore h.toLawsCore j ka 7 Tn
    (cc D large₂ C2 A2 7 wL) large₂ H.CK 1 4 (C₀ H.CA 7 H.CK) 4 1041 3
    hG hj hjm hL (GlobalTheory.ArcCM.killQ_of_gamAt hK D T.toCore h.toLawsCore j ka 7 Tn _ hG hj hjm)
    (GlobalTheory.ArcCM.detectQ_of_known hK D T.toCore h.toLawsCore j ka 7 Tn _ hG hj hjm h3 hT hc)
    hZ (hC₀ _ _ _) (by norm_num) hR
    (le_trans hdim hpp)
  have e4 : max (4 : ℝ) (max 4 3) = 4 := by norm_num
  rw [e4] at key
  exact key hCR hO hn hlast hsz hT hc hTc

end GlobalTheory.RunJoin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RecursivePageLatticeBoundStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

theorem _root_.GlobalTheory.T.recursive_page_lattice_bound : ∃ Cq : ℝ → ℝ → ℝ, ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → j < D.R.m → LatAt (recB h.toLawsCore) j ka → QAt large₂ (recB h.toLawsCore) j ka 7 H.CK 1 4 (Cq H.CA H.CK) 4 Tn (cc D large₂ C2 A2 7 wL) := by
  first | exact @GlobalTheory.RunJoin.qAt_run | exact GlobalTheory.RunJoin.qAt_run | (intros; apply GlobalTheory.RunJoin.qAt_run <;> assumption)
end
end
