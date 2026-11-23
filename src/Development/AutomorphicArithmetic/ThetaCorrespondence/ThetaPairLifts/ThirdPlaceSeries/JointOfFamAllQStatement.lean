module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamAllQ
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawTransportRelationsOfFamilyLawsStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ReductionLemmaFirst
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.RatioUnit

theorem natCast_notMem_of_primes {R : Type} [CommRing R] (P : Ideal R) [hP : P.IsPrime] :
    ∀ m : ℕ, m ≠ 0 → (∀ p : ℕ, p.Prime → p ∣ m → (p : R) ∉ P) → (m : R) ∉ P := by
  intro m
  induction m using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one => intro _ _; rw [Nat.cast_one]; exact fun h => hP.ne_top ((Ideal.eq_top_iff_one P).2 h)
  | prime p hp => intro _ h; exact h p hp dvd_rfl
  | mul a b ha hb =>
    intro hab h hmem
    rw [Nat.cast_mul] at hmem
    rcases hP.mem_or_mem hmem with h1 | h1
    · exact ha (left_ne_zero_of_mul hab) (fun p hp hd => h p hp (dvd_mul_of_dvd_left hd b)) h1
    · exact hb (right_ne_zero_of_mul hab) (fun p hp hd => h p hp (dvd_mul_of_dvd_right hd a)) h1

theorem not_dvd_both {r : ℚ} {p : ℕ} (hp : p.Prime) (h1 : p ∣ r.num.natAbs) (h2 : p ∣ r.den) : False :=
  hp.not_dvd_one (by simpa [Nat.Coprime.gcd_eq_one r.reduced] using Nat.dvd_gcd h1 h2)

theorem padicValRat_ne_zero_of_dvd_num {r : ℚ} (hr : r ≠ 0) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ r.num.natAbs) : padicValRat p r ≠ 0 := by
  haveI := Fact.mk hp
  have hnd : ¬ p ∣ r.den := fun hd' => not_dvd_both hp hd hd'
  have h0 : r.num.natAbs ≠ 0 := by simpa using hr
  have h1 := one_le_padicValNat_of_dvd h0 hd
  simp only [padicValRat, padicValInt, padicValNat.eq_zero_of_not_dvd hnd]
  omega

theorem padicValRat_ne_zero_of_dvd_den {r : ℚ} {p : ℕ} (hp : p.Prime)
    (hd : p ∣ r.den) : padicValRat p r ≠ 0 := by
  haveI := Fact.mk hp
  have hnd : ¬ p ∣ r.num.natAbs := fun hd' => not_dvd_both hp hd' hd
  have h1 := one_le_padicValNat_of_dvd r.den_nz hd
  simp only [padicValRat, padicValInt, padicValNat.eq_zero_of_not_dvd hnd]
  omega

end GlobalTheory.Fam.RatioUnit

namespace GlobalTheory.Fam
open Formalism.DivisionValues GlobalTheory.Fam.RatioUnit

theorem RatioUnit.intCast_notMem_of_natAbs {R : Type} [CommRing R] (P : Ideal R) (z : ℤ)
    (h : ((z.natAbs : ℕ) : R) ∉ P) : ((z : ℤ) : R) ∉ P := by
  rcases Int.natAbs_eq z with e | e
  · rw [e]; simpa using h
  · rw [e]; simpa [Ideal.neg_mem_iff] using h

theorem vw_eq_zero_of_unitRatio : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (w : HeightOneSpectrum (𝓞 K)) (S : ℕ → Prop) (x y : ℂ), GlobalTheory.Fam.UnitRatio S x y → (∀ p : ℕ, p.Prime → S p → (p : 𝓞 K) ∉ w.asIdeal) → ∀ a : K, σ a = x / y → Formalism.DivisionValues.vw w a = 0 := by
  intro K _ _ σ w S x y hU hS a ha

  letI : StarRing K := starRingOfComm
  obtain ⟨_, n, hn, r, hr0, hpow, hrS⟩ := hU
  have hpow' : a ^ n = (r : K) := by
    apply σ.injective
    rw [map_pow, ha, hpow, map_ratCast]
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hpow'
    exact hr0 (by exact_mod_cast hpow'.symm)
  have hnum : ((r.num : ℤ) : 𝓞 K) ∉ w.asIdeal := by
    refine intCast_notMem_of_natAbs _ _ (natCast_notMem_of_primes w.asIdeal _ (by simpa using hr0) ?_)
    intro p hp hd
    exact hS p hp (hrS p hp (padicValRat_ne_zero_of_dvd_num hr0 hp hd))
  have hden : ((r.den : ℕ) : 𝓞 K) ∉ w.asIdeal := by
    refine natCast_notMem_of_primes w.asIdeal _ r.den_nz ?_
    intro p hp hd
    exact hS p hp (hrS p hp (padicValRat_ne_zero_of_dvd_den hp hd))
  have vnum := ReductionFirst.vw_unit w _ hnum
  have vden := ReductionFirst.vw_unit w _ hden
  rw [show (((r.num : ℤ) : 𝓞 K) : K) = (r.num : K) from map_intCast (algebraMap (𝓞 K) K) _] at vnum
  rw [show (((r.den : ℕ) : 𝓞 K) : K) = (r.den : K) from map_natCast (algebraMap (𝓞 K) K) _] at vden
  have hd0 : (r.den : K) ≠ 0 := by exact_mod_cast r.den_nz
  have hrK0 : (r : K) ≠ 0 := by exact_mod_cast hr0
  have key : (r : K) * (r.den : K) = (r.num : K) := by
    rw [Rat.cast_def]; field_simp
  have h1 := ReductionFirst.vw_mul w hrK0 hd0
  rw [key, vnum, vden] at h1
  have h2 := ReductionFirst.vw_pow w a n
  rw [hpow'] at h2
  have h3 : (n : ℤ) * vw w a = 0 := by rw [← h2]; omega
  rcases mul_eq_zero.1 h3 with h | h
  · exact absurd (by exact_mod_cast h) hn.ne'
  · exact h

end GlobalTheory.Fam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatioStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.valuation_eq_zero_of_rootOfSUnitRatio : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (w : HeightOneSpectrum (𝓞 K)) (S : ℕ → Prop) (x y : ℂ), GlobalTheory.Fam.UnitRatio S x y → (∀ p : ℕ, p.Prime → S p → (p : 𝓞 K) ∉ w.asIdeal) → ∀ a : K, σ a = x / y → Formalism.DivisionValues.vw w a = 0 := by
  first | exact @GlobalTheory.Fam.vw_eq_zero_of_unitRatio | exact GlobalTheory.Fam.vw_eq_zero_of_unitRatio | (intros; apply GlobalTheory.Fam.vw_eq_zero_of_unitRatio <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RelOfLinks

section

@[expose] public section



section
noncomputable section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
namespace GlobalTheory.MiTop
theorem rel_of_links_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (d : _root_.GlobalTheory.MiTop.BottomData W u), (∀ t, (f.t t).Is) → MainX f.t → _root_.GlobalTheory.MiTop.LinkVanishes f d → _root_.GlobalTheory.MiTop.LinkTailCondition f → _root_.GlobalTheory.MiTop.LinkDescends f → _root_.GlobalTheory.MiTop.LinkSurjective f → _root_.GlobalTheory.MiTop.LinkCommutes f → _root_.GlobalTheory.MiTop.FamilyRatioCondition f → _root_.GlobalTheory.MiTop.FamilyServedCondition W → ∃ (U : D.what₂.Mu u →ₗ[ℂ] D.what₂.Mu u) (r : ℝ) (c : W.P.T → ℂ), 0 < r ∧ (∀ φ, ‖U φ‖ = r * ‖φ‖) ∧ _root_.GlobalTheory.MiTop.UnitCoefficients W c ∧ d.Rel U c := by
  intro D L hT Gi Gl Kc Yd cX ex W u f d hIs hMain hZ hTail hDown hOnto hComm hRat hServ
  obtain ⟨a, ha⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  obtain ⟨n, hn⟩ : ∃ n, 2 * n + 2 = D.R.m := ⟨a - 1, by omega⟩
  have h : 2 * n + 2 * 0 + 2 = D.R.m := by omega
  have h₀ : 0 + 2 * n + 2 = D.R.m := by omega
  have hN : 2 * (n + 1) = D.R.m := by omega
  obtain ⟨S, r, s, hr, hS, hs, hcomm⟩ := hComm (n + 1) hN
  have hBot : ∀ t, (f.t t).cBot ≠ 0 := fun t =>
    Finset.prod_ne_zero_iff.mpr (fun j hj => (hIs t).cI j (Finset.mem_range.mp hj))
  have hTop : ∀ t, (f.t t).cTop (n + 1) ≠ 0 := fun t => (hRat (n + 1) hN t).1
  refine ⟨(S.symm : D.what₂.Mu u →ₗ[ℂ] D.what₂.Mu u), r⁻¹, fun t => (f.t t).cTop (n + 1) * s / (f.t t).cBot,
    inv_pos.mpr hr, ?_, ?_, ?_⟩
  · intro φ
    have e := hS (S.symm φ)
    simp only [LinearEquiv.apply_symm_apply] at e
    simp only [LinearEquiv.coe_coe]
    rw [e, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  · refine ⟨fun t => div_ne_zero (mul_ne_zero (hTop t) hs) (hBot t), ?_⟩
    intro w k hk
    refine GlobalTheory.T.valuation_eq_zero_of_rootOfSUnitRatio D.what₂.LL D.what₂.embLL w (_root_.GlobalTheory.MiTop.qPrime_alt W (W.Q.Rl.mu w)) _ _ (hRat (n + 1) hN (W.Q.Rl.mu w)).2
      (fun p hp hb => hServ w p hp hb) k ?_
    rw [hk]
    have a1 := hTop (W.Q.Rl.mu w)
    have a2 := hTop W.P.A3.A.μ0
    have b1 := hBot (W.Q.Rl.mu w)
    have b2 := hBot W.P.A3.A.μ0
    field_simp
  · intro T hT0
    obtain ⟨G₀, hG₀⟩ := hOnto n h T hT0
    refine ⟨fun φ₀ => (f.t W.P.A3.A.μ0).cTop (n + 1) * (f.t W.P.A3.A.μ0).tail (2 * (n + 1)) hN
      ((f.t W.P.A3.A.μ0).up (n + 1) (_root_.GlobalTheory.MiTop.col0_alt f W.P.A3.A.μ0 (S.symm φ₀))) G₀ / (f.t W.P.A3.A.μ0).cBot, ?_⟩
    intro φ₀ φ t F F' hFF α α' hrel y v
    obtain ⟨G, hG1, hGd⟩ := hDown n h t F'
    let sB : Bool → W.P.T := fun b => Bool.rec t W.P.A3.A.μ0 b
    let xB : Bool → D.what₂.Mu u := fun b => Bool.rec (S.symm φ) (S.symm φ₀) b
    let aB : Bool → ℂ := fun b => Bool.rec (α' / (f.t t).cBot) (α / (f.t W.P.A3.A.μ0).cBot) b
    let FB : ∀ b, (f.t (sB b)).CT := fun b => Bool.rec (motive := fun b => (f.t (sB b)).CT) G G₀ b
    have key := hMain n h h₀ Bool sB aB (fun b => _root_.GlobalTheory.MiTop.col0_alt f (sB b) (xB b)) FB
      (fun b => ((hZ n h₀ (sB b) (xB b)).1))
    rw [Fintype.sum_bool] at key
    have top : aB true * (f.t (sB true)).cTop (n + 1) * (f.t (sB true)).tail (2 * (n + 1)) h
          ((f.t (sB true)).up (n + 1) (_root_.GlobalTheory.MiTop.col0_alt f (sB true) (xB true))) (FB true) +
        aB false * (f.t (sB false)).cTop (n + 1) * (f.t (sB false)).tail (2 * (n + 1)) h
          ((f.t (sB false)).up (n + 1) (_root_.GlobalTheory.MiTop.col0_alt f (sB false) (xB false))) (FB false) = 0 := by
      have e1 := hcomm t (S.symm φ) G
      rw [LinearEquiv.apply_symm_apply] at e1
      have e2 := hTail (n + 1) hN t φ F F' hFF G hG1
      change α / (f.t W.P.A3.A.μ0).cBot * (f.t W.P.A3.A.μ0).cTop (n + 1) * (f.t W.P.A3.A.μ0).tail (2 * (n + 1)) hN
          ((f.t W.P.A3.A.μ0).up (n + 1) (_root_.GlobalTheory.MiTop.col0_alt f W.P.A3.A.μ0 (S.symm φ₀))) G₀ +
        α' / (f.t t).cBot * (f.t t).cTop (n + 1) * (f.t t).tail (2 * (n + 1)) hN ((f.t t).up (n + 1) (_root_.GlobalTheory.MiTop.col0_alt f t (S.symm φ))) G = 0
      rw [e1, e2]
      beta_reduce at hrel
      linear_combination hrel
    have bot := key top y v
    rw [Fintype.sum_bool] at bot
    have z1 := (hZ n h₀ W.P.A3.A.μ0 (S.symm φ₀)).2
      ((f.t W.P.A3.A.μ0).dn (2 * n + 1) ((f.t W.P.A3.A.μ0).ioT (2 * n) h G₀)) y v
    have z2 := (hZ n h₀ t (S.symm φ)).2 ((f.t t).dn (2 * n + 1) ((f.t t).ioT (2 * n) h G)) y v
    change α / (f.t W.P.A3.A.μ0).cBot * (f.t W.P.A3.A.μ0).cBot * (f.t W.P.A3.A.μ0).per 0 n h₀ (_root_.GlobalTheory.MiTop.col0_alt f W.P.A3.A.μ0 (S.symm φ₀))
        ((f.t W.P.A3.A.μ0).dn (2 * n + 1) ((f.t W.P.A3.A.μ0).ioT (2 * n) h G₀)) y v +
      α' / (f.t t).cBot * (f.t t).cBot * (f.t t).per 0 n h₀ (_root_.GlobalTheory.MiTop.col0_alt f t (S.symm φ))
        ((f.t t).dn (2 * n + 1) ((f.t t).ioT (2 * n) h G)) y v = 0 at bot
    rw [z1, z2] at bot
    have d1 : ((f.t W.P.A3.A.μ0).dn (2 * n + 1) ((f.t W.P.A3.A.μ0).ioT (2 * n) h G₀)).1 = T := hG₀
    have d2 : ((f.t t).dn (2 * n + 1) ((f.t t).ioT (2 * n) h G)).1 = _root_.GlobalTheory.MiTop.rowFormOfTuple W t F' := hGd
    rw [d1, d2, div_mul_cancel₀ _ (hBot _), div_mul_cancel₀ _ (hBot _)] at bot
    simpa only [LinearEquiv.coe_coe] using bot
end GlobalTheory.MiTop
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JointOfFamAllQ

section

@[expose] public section



section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
namespace GlobalTheory.MiTop
theorem joint_of_famAllQ_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.FamilyAllConditions W → _root_.GlobalTheory.MiTop.FamilyServedCondition W → _root_.GlobalTheory.MiTop.JointCondition W := by
  intro hCusp hHC D L hT Gi Gl Kc Yd cX ex W hFam hServ
  obtain ⟨z, hz, hzc, hu⟩ := hFam
  refine ⟨z, hz, hzc, fun u => ?_⟩
  obtain ⟨f, d, hPin, hLaws, hZ, hTail, hDown, hOnto, hComm, hRat⟩ := hu u
  have hMain : MainX f.t := GlobalTheory.T.seesawTransportRelations_of_familyLaws hCusp hHC D _ _ f.t hLaws
  obtain ⟨U, r, c, hr, hU, hc, hRel⟩ :=
    _root_.GlobalTheory.MiTop.rel_of_links_alt W u f d hLaws.tup hMain hZ hTail hDown hOnto hComm hRat hServ
  exact ⟨d, U, r, c, hPin, hr, hU, hc, hRel⟩
end GlobalTheory.MiTop
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JointOfFamAllQStatement

section

@[expose] public section



section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.joint_of_famAllQ_of_servedQ : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.FamilyAllConditions W → _root_.GlobalTheory.MiTop.FamilyServedCondition W → _root_.GlobalTheory.MiTop.JointCondition W := by
  first | exact @_root_.GlobalTheory.MiTop.joint_of_famAllQ_alt | exact _root_.GlobalTheory.MiTop.joint_of_famAllQ_alt | (intros; apply _root_.GlobalTheory.MiTop.joint_of_famAllQ_alt <;> assumption)
end
end
end
