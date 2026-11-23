module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSuppOnIffIdemMulOfNatural
import Formalism.LocalToGlobal.ProjectiveLattices.CompFin
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeySectionFourthRootPerComponent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitSectionThetaKeyRuleWeightFour
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdConjDifferentEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleValuationNonnegIntegralFramedPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionValuationBoundsDifferent
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyFamOne
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstantSmulIntegralOfFourthPower

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option synthInstance.maxHeartbeats 400000

noncomputable section
namespace GlobalTheory.RuleIntegral

theorem vLa_int_nonneg {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {r : 𝓞 K}
    (hr : (r : K) ≠ 0) : 0 ≤ vLa w (r : K) := by
  unfold vLa
  have h1 := w.valuation_le_one (K := K) r
  have h2 : (w.valuation K) (r : K) ≠ 0 := (Valuation.ne_zero_iff _).mpr hr
  have h3 := (WithZero.log_le_log h2 one_ne_zero).mpr h1
  rw [WithZero.log_one] at h3
  omega

theorem nonneg_of_four {x : EReal} (hx : x ≠ ⊥) (h : 0 ≤ x + x + x + x) : 0 ≤ x := by
  induction x using EReal.rec with
  | bot => exact absurd rfl hx
  | top => exact le_top
  | coe r =>
    have : (0 : EReal) ≤ ((r + r + r + r : ℝ) : EReal) := by simpa [EReal.coe_add] using h
    have h' : (0 : ℝ) ≤ r + r + r + r := EReal.coe_nonneg.1 this
    exact EReal.coe_nonneg.2 (by linarith)

theorem eq_zero_or_top_of_double {x : EReal} (hx : x ≠ ⊥) (h : x = x + x) : x = 0 ∨ x = ⊤ := by
  induction x using EReal.rec with
  | bot => exact absurd rfl hx
  | top => exact Or.inr rfl
  | coe r =>
    left
    have h' : r = r + r := by exact_mod_cast h
    have : r = 0 := by linarith
    simp [this]

theorem exists_common_denom {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] (a : ι → K) :
    ∃ s : 𝓞 K, (s : K) ≠ 0 ∧ ∀ i, ∃ r : 𝓞 K, (r : K) = (s : K) * a i := by
  classical
  have h := fun i => IsLocalization.exists_integer_multiple (nonZeroDivisors (𝓞 K)) (a i)
  choose d hd using h
  refine ⟨∏ i, (d i : 𝓞 K), ?_, fun i => ?_⟩
  · have hm : (∏ i, (d i : 𝓞 K)) ∈ nonZeroDivisors (𝓞 K) :=
      Submonoid.prod_mem _ fun i _ => (d i).2
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hm
  · obtain ⟨r, hr⟩ := hd i
    refine ⟨(∏ j ∈ Finset.univ.erase i, (d j : 𝓞 K)) * r, ?_⟩
    rw [← Finset.mul_prod_erase Finset.univ (fun j => (d j : 𝓞 K)) (Finset.mem_univ i)]
    have e1 : ∀ x : 𝓞 K, (x : K) = algebraMap (𝓞 K) K x := fun _ => rfl
    rw [e1, e1, map_mul, map_mul, hr, Algebra.smul_def]
    ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_idem_zero {w : HeightOneSpectrum (𝓞 c.F)} {v : Rul Xo c → EReal}
    (hv : v ∈ valSet Xo c (algCls Xo c) w) : ∃ Z, v (GlobalTheory.FlatLine.idem Z) = 0 := by
  obtain ⟨y, rfl⟩ := hv
  have h1 : vAtV y 1 = 0 := by
    rcases y with ⟨q, T, io, e, ho, y, hy, eta, heta, rfl⟩
    show nval T.V e (evI y 1) = 0
    have h1 : evI y 1 = 1 := by
      letI := io.toAlgebra
      exact evalAt_one _ _ y.1 y.2.1
    rw [h1, nval_of_ne one_ne_zero]
    simp [vV]
  by_contra hne
  push_neg at hne
  have htop : ∀ Z, vAtV y (GlobalTheory.FlatLine.idem Z) = ⊤ := fun Z => by
    have hd := vAtV_mul y (GlobalTheory.FlatLine.idem Z) (GlobalTheory.FlatLine.idem Z)
    rw [GlobalTheory.FlatLine.idem_mul_idem] at hd
    exact (eq_zero_or_top_of_double (vAtV_ne_bot y _) hd).resolve_left (hne Z)
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)
  classical
  have hs : ∀ s : Finset (Comp Xo c), vAtV y (∑ Z ∈ s, GlobalTheory.FlatLine.idem Z) = ⊤ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using vAtV_zero y
    | insert Z s hZ ih =>
      rw [Finset.sum_insert hZ]
      have := vAtV_add y (GlobalTheory.FlatLine.idem Z) (∑ Z ∈ s, GlobalTheory.FlatLine.idem Z)
      rw [htop Z, ih, min_self] at this
      exact top_le_iff.1 this
  have h2 := hs Finset.univ
  rw [GlobalTheory.FlatLine.sum_idem] at h2
  rw [h2] at h1
  exact EReal.top_ne_zero h1

theorem exists_smul_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K ρ : Rul Xo c) (a : Comp Xo c → c.F), (∀ Z, a Z ≠ 0) → (∀ Z, GlobalTheory.FlatLine.idem Z * ρ ^ 4 = a Z • (GlobalTheory.FlatLine.idem Z * K)) → (∀ (w : HeightOneSpectrum (𝓞 c.F)), ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v K) → ∃ t : c.F, t ≠ 0 ∧ ∀ (w : HeightOneSpectrum (𝓞 c.F)), ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v (t • ρ) := by
  intro E _ _ _ H Dw l Xo c K ρ a ha hρ hK
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)
  obtain ⟨s, hs0, hsa⟩ := exists_common_denom a
  refine ⟨(s : c.F), hs0, fun w v hv => ?_⟩
  have hKv := hK w v hv
  obtain ⟨Z, hZ⟩ := exists_idem_zero hv
  obtain ⟨y, rfl⟩ := hv
  obtain ⟨r, hr⟩ := hsa Z
  have hb : (((s ^ 3 * r : 𝓞 c.F)) : c.F) = (s : c.F) ^ 4 * a Z := by
    have hr' : algebraMap (𝓞 c.F) c.F r = algebraMap (𝓞 c.F) c.F s * a Z := hr
    show algebraMap (𝓞 c.F) c.F (s ^ 3 * r) = (algebraMap (𝓞 c.F) c.F s) ^ 4 * a Z
    rw [map_mul, map_pow, hr']; ring
  have hb0 : (((s ^ 3 * r : 𝓞 c.F)) : c.F) ≠ 0 := by
    rw [hb]; exact mul_ne_zero (pow_ne_zero _ hs0) (ha Z)
  have hid : GlobalTheory.FlatLine.idem Z * ((s : c.F) • ρ) ^ 4 =
      (((s ^ 3 * r : 𝓞 c.F)) : c.F) • (GlobalTheory.FlatLine.idem Z * K) := by
    rw [smul_pow, mul_smul_comm, hρ Z, smul_smul, hb]
  have h4 : ∀ x : Rul Xo c, x ^ 4 = x * x * x * x := fun x => by ring
  have e := congrArg (vAtV y) hid
  rw [h4, vAtV_mul, vAtV_mul, vAtV_mul, vAtV_mul, vAtV_smul _ _ _ hb0, vAtV_mul, hZ, zero_add, zero_add] at e
  refine nonneg_of_four (vAtV_ne_bot _ _) ?_
  rw [e]
  refine add_nonneg ?_ hKv
  exact EReal.coe_nonneg.2 (by exact_mod_cast vLa_int_nonneg w hb0)

end GlobalTheory.RuleIntegral
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstantSmulIntegralOfFourthPowerStatement

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem _root_.GlobalTheory.T.exists_constant_smul_integral_of_fourth_power : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K ρ : Rul Xo c) (a : Comp Xo c → c.F), (∀ Z, a Z ≠ 0) → (∀ Z, GlobalTheory.FlatLine.idem Z * ρ ^ 4 = a Z • (GlobalTheory.FlatLine.idem Z * K)) → (∀ (w : HeightOneSpectrum (𝓞 c.F)), ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v K) → ∃ t : c.F, t ≠ 0 ∧ ∀ (w : HeightOneSpectrum (𝓞 c.F)), ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v (t • ρ) := by
  first | exact @GlobalTheory.RuleIntegral.exists_smul_nonneg | exact GlobalTheory.RuleIntegral.exists_smul_nonneg | (intros; apply GlobalTheory.RuleIntegral.exists_smul_nonneg <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsInverseIntegralInvariant

section

@[expose] public section

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.KeyInvInt
open GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FlatLine

theorem exists_inverse_integral_invariant : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∃ (u u' : Rul Y.d.Xo₂ Y.d.c₂) (t : Y.d.c₂.F), u ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) 0 1) ∧ t ≠ 0 ∧ u * u' = t • 1 ∧ ∀ la', ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la', 0 ≤ v u' := by
  intro _hP D T j Y e o hY _hE
  have hσ := goodEmb_goodOf Y.d.c₂ Y.d.c₂.F.val.toRingHom
  obtain ⟨hr, -, -, -, -, g, ee, F, -⟩ := hY.unf _ hσ
  have h1 : 1 ≤ D.R.r := by
    have := D.R.two_le_m
    unfold Formalism.BasicNotions.Ranks.r
    omega
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by omega
  obtain ⟨κ, k₁, k₂, k₃, k₄, k₅, k₆, -, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  obtain ⟨K, hK, hKv⟩ := GlobalTheory.KeyFourth.exists_unit_secZ_keyRule κ k₁ k₂ k₆ _ _ _ _ _ _ g ee hpq
  obtain ⟨ρ, hρ⟩ := GlobalTheory.KeyRoot.exists_keySec_pow_four κ k₁ k₂ k₆ k₄ _ _ _ _ _ _ g ee _ _ (Y.U _) K hσ
    (hY.unf _ hσ) hY.geo hpq hK hKv
  choose a ha hZ using hρ
  have hkr : GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.IsKeyRule κ := by
    refine ⟨?_, k₂, k₃, k₄, ?_⟩
    · simpa only [GlobalTheory.KeyCl.Homog, mul_one] using k₁
    · simpa only [GlobalTheory.KeyCl.ArchNorm, mul_one] using k₅
  have hKint : ∀ (w : IsDedekindDomain.HeightOneSpectrum (𝓞 Y.d.c₂.F)),
      ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) w, 0 ≤ v (K : Rul Y.d.Xo₂ Y.d.c₂) := by
    by_cases hg : ∀ p : ℕ, p.Prime → Y.d.l₂.GoodAt p
    · exact fun w v hv => (GlobalTheory.KeyIntegralVal.key_valuation_bounds κ hkr _ _ _ _ _ _ g ee K hpq hg hK hKv w v hv).1
    · exact GlobalTheory.T.thetaKeyRule_valuation_nonneg_integral_framed_point κ hkr _ _ _ _ _ _ g ee K hpq hK hKv
  obtain ⟨t, ht, hint⟩ := GlobalTheory.T.exists_constant_smul_integral_of_fourth_power _ _ _ _ _ _ (K : Rul Y.d.Xo₂ Y.d.c₂) (ρ.ρ : Rul Y.d.Xo₂ Y.d.c₂) a ha hZ hKint
  have hwt : ∀ (m : ℤ) (τ : D.host.E →+* ℂ) (i : ℕ), i < (T.Q.Dw j).mult τ → (wtOf (T.Q.Dw j) 0 m).1 (τ, i) = -m :=
    GlobalTheory.KeyRootTw.wtOf_zero_fst _ _ (T.Q.Dw j)
  have hex : GlobalTheory.AllWt.exOf (T.Q.Dw j) 0 1 = -keyEx (T.Q.Dw j) := by
    funext i
    rcases i with _ | ⟨τ, i⟩
    · rfl
    · simp only [GlobalTheory.AllWt.exOf, exZ, keyEx, Pi.neg_apply]
      exact hwt 1 τ i i.2
  refine ⟨((ρ.ρ⁻¹ : (Rul Y.d.Xo₂ Y.d.c₂)ˣ) : Rul Y.d.Xo₂ Y.d.c₂), t • (ρ.ρ : Rul Y.d.Xo₂ Y.d.c₂), t, ?_, ht, ?_, hint⟩
  · rw [hex]
    exact GlobalTheory.AllWt.inv_mem_secZ ρ.mem
  · rw [mul_smul_comm, Units.inv_mul]
end GlobalTheory.KeyInvInt
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp


theorem _root_.GlobalTheory.T.inverse_invariant_integral : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∃ (u u' : Rul Y.d.Xo₂ Y.d.c₂) (t : Y.d.c₂.F), u ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) 0 1) ∧ t ≠ 0 ∧ u * u' = t • 1 ∧ ∀ la', ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la', 0 ≤ v u' := by
  first | exact @_root_.GlobalTheory.KeyInvInt.exists_inverse_integral_invariant | exact _root_.GlobalTheory.KeyInvInt.exists_inverse_integral_invariant | (intros; apply _root_.GlobalTheory.KeyInvInt.exists_inverse_integral_invariant <;> assumption)
end
end
end
