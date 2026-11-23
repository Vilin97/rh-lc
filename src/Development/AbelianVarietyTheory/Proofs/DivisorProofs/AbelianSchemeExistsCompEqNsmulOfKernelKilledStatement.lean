module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankQuotKerIdealDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardLPowerTorsionKernelEqLPartIsogenyDegreeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsogenyKernelFiniteAlgebraFinrankEqDegree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKernelPartOrderPrimeToP
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffFiniteKer
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientOfGaloisStableFiniteSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffFiniteKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoIffDegEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyCompIffAndDegreeMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyDegreeEqCardKernelOfKilledByInvertible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfIsFiniteOfDimEqAbelianVarietyHom

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInverseDeg

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar.InvDegInverse

variable {K : Type} [Field K]

def invKer {A B : AbVar K} (f : A ⟶ B) : Subgroup A.Pt where
  carrier := {x | ptMap f x = 1 ∧ ∃ k : ℕ, (k : K) ≠ 0 ∧ x ^ k = 1}
  one_mem' := ⟨map_one _, 1, by simp, one_pow _⟩
  mul_mem' := by
    rintro x y ⟨hx, a, ha, hxa⟩ ⟨hy, b, hb, hyb⟩
    refine ⟨by rw [map_mul, hx, hy, _root_.one_mul], a * b, by push_cast; exact mul_ne_zero ha hb, ?_⟩
    rw [mul_pow, pow_mul, hxa, one_pow, mul_comm a b, pow_mul, hyb, one_pow, _root_.one_mul]
  inv_mem' := by
    rintro x ⟨hx, a, ha, hxa⟩
    exact ⟨by rw [map_inv, hx, inv_one], a, ha, by rw [inv_pow, hxa, inv_one]⟩

theorem finite_invKer {A B : AbVar K} (f : A ⟶ B) (hf : IsIsogeny f) : Finite (invKer f) := by
  have : Finite (ptMap f).ker := (GlobalTheory.AV.AbVar.isFinite_iff_finite_ker K A B f).1 hf.1
  exact Finite.of_injective (fun x : invKer f => (⟨x.1, x.2.1⟩ : (ptMap f).ker))
    (fun x y h => Subtype.ext (congrArg (fun z : (ptMap f).ker => (z : A.Pt)) h))

theorem card_invKer_ne_zero {A B : AbVar K} (f : A ⟶ B) (hf : IsIsogeny f) :
    ((Nat.card (invKer f) : ℕ) : K) ≠ 0 := by
  haveI := finite_invKer f hf
  intro h0
  have hpos : 0 < Nat.card (invKer f) := Nat.card_pos
  have hpd : ringChar K ∣ Nat.card (invKer f) := (ringChar.spec K _).1 h0
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hpp | hp0
  · haveI := Fact.mk hpp
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (ringChar K) hpd
    obtain ⟨_, k, hk, hyk⟩ := y.2
    have : ringChar K ∣ k := by
      rw [← hy, ← Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one hyk
    exact hk ((ringChar.spec K k).2 this)
  · rw [hp0, zero_dvd_iff] at hpd
    omega

theorem galPts_mem_invKer {A B : AbVar K} (f : A ⟶ B) (σ : Gal K) (x : A.Pt) (hx : x ∈ invKer f) :
    galPts A.X σ x ∈ invKer f := by
  obtain ⟨h1, k, hk, hxk⟩ := hx
  refine ⟨?_, k, hk, by rw [← map_pow, hxk, map_one]⟩
  have e : ptMap f (galPts A.X σ x) = galPts B.X σ (ptMap f x) :=
    show (specAut σ ≫ x) ≫ f.hom = specAut σ ≫ (x ≫ f.hom) from Category.assoc _ _ _
  rw [e, h1, map_one]

end GlobalTheory.AV.AbVar.InvDegInverse
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeExistsCompEqNsmulOfKernelKilled

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar.KilledInverse

open GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.AV.KerPart GlobalTheory.AV.AbVar.InvDegInverse

variable {k : Type} [Field k]

theorem exists_kerPow_finrank_ne_zero {A B : AbVar k} (f : A ⟶ B) (e : ℕ) (he : IsUnit (e : k)) :
    ∃ (H : Type) (_ : CommRing H) (_ : Algebra k H) (i : ptOver k H ⟶ A.X),
      KerPow f e H i ∧ ((Module.finrank k H : ℕ) : k) ≠ 0 := by
  have he0 : (e : k) ≠ 0 := he.ne_zero
  have hepos : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; exact he0 Nat.cast_zero)

  have key : ∃ p : ℕ, p.Prime ∧ ¬ p ∣ e ∧ ∀ n : ℕ, ¬ p ∣ n → (n : k) ≠ 0 := by
    rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | hp0
    · refine ⟨ringChar k, hp, fun h => he0 ((ringChar.spec k e).2 h), fun n hn h0 => hn ((ringChar.spec k n).1 h0)⟩
    · obtain ⟨p, hpe, hp⟩ := Nat.exists_infinite_primes (e + 1)
      refine ⟨p, hp, fun h => ?_, fun n hn h0 => ?_⟩
      · have := Nat.le_of_dvd hepos h
        omega
      · have h1 := (ringChar.spec k n).1 h0
        rw [hp0, zero_dvd_iff] at h1
        exact hn (h1 ▸ dvd_zero p)
  obtain ⟨p, hp, hpe, hpk⟩ := key
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨H, _, _, i, hi, hH⟩ := exists_kerPow_not_dvd p k A B f e hepos hpe
  exact ⟨H, inferInstance, inferInstance, i, hi, hpk _ hH⟩

theorem finite_ker_of_kerPow {A B : AbVar k} (f : A ⟶ B) (e : ℕ) {H : Type} [CommRing H] [Algebra k H]
    {i : ptOver k H ⟶ A.X} (hi : KerPow f e H i) (hH : Module.finrank k H ≠ 0)
    (hkill : ∀ (T : Over (Sp k)) (x : T ⟶ A.X), x ≫ f.hom = 1 → x ^ e = 1) : Finite (ptMap f).ker := by
  haveI : Module.Finite k H := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hH)
  have hx : ∀ x : (ptMap f).ker, x.1 ≫ f.hom = 1 := fun x => MonoidHom.mem_ker.mp x.2
  let φ : (ptMap f).ker → (H →ₐ[k] AlgebraicClosure k) := fun x =>
    (hi.2 (AlgebraicClosure k) x.1 (hx x) (hkill _ x.1 (hx x))).exists.choose
  have hφ : ∀ x, spMap (φ x).toRingHom ≫ i.left = x.1.left := fun x =>
    (hi.2 (AlgebraicClosure k) x.1 (hx x) (hkill _ x.1 (hx x))).exists.choose_spec
  refine Finite.of_injective φ fun x y hxy => ?_
  apply Subtype.ext
  apply Over.OverMorphism.ext
  rw [← hφ x, ← hφ y, hxy]

theorem exists_comp_eq_nsmul (A B : AbVar k) (f : A ⟶ B) (hdim : A.dim = B.dim) (e : ℕ) (he : IsUnit (e : k))
    (hkill : ∀ (T : Over (Sp k)) (x : T ⟶ A.X), x ≫ f.hom = 1 → x ^ e = 1) :
    ∃ m : B ⟶ A, f ≫ m = e • 𝟙 A := by
  obtain ⟨H, _, _, i, hi, hH⟩ := exists_kerPow_finrank_ne_zero f e he
  have hH0 : Module.finrank k H ≠ 0 := fun h0 => hH (by rw [h0, Nat.cast_zero])
  have hfin : IsFinite f.hom.left :=
    (isFinite_iff_finite_ker k A B f).2 (finite_ker_of_kerPow f e hi hH0 hkill)
  have hf : IsIsogeny f := ⟨hfin, surjective_of_isFinite_of_dim_eq k A B f hdim hfin⟩
  have hd : ((deg f : ℕ) : k) ≠ 0 := by
    obtain ⟨H0, _, _, i0, hi0, h0⟩ := exists_kerPow_zero_finrank_eq_deg k A B f hf
    rw [← h0, finrank_eq_of_kerPow hi0 hi (fun R _ _ x hx => ⟨fun _ => hkill _ x hx, fun _ => pow_zero x⟩)]
    exact hH
  haveI hGfin := finite_invKer f hf
  obtain ⟨C, q, hq, hdq, hker, huniv⟩ := GlobalTheory.T.exists_quotient_of_galoisStable_finite_subgroup k A (invKer f) hGfin (card_invKer_ne_zero f hf)
    (galPts_mem_invKer f)
  obtain ⟨h, hqh⟩ := huniv B f (fun x hx => hx.1)
  have hdimAC := (GlobalTheory.AV.AbVar.isogeny_flat_finrank k A C q hq).1
  have hdimAB := (GlobalTheory.AV.AbVar.isogeny_flat_finrank k A B f hf).1
  have hcomp := GlobalTheory.AV.AbVar.isIsogeny_comp_iff_and_deg_comp k A C B q h hdimAC (hdimAC.symm.trans hdimAB)
  rw [hqh] at hcomp
  have hdeg : deg f = deg q * deg h := hcomp.2
  have hv : ∀ l : ℕ, l.Prime → (l : k) ≠ 0 → padicValNat l (deg f) = padicValNat l (deg q) := by
    intro l hl hlK
    haveI := Fact.mk hl
    have e1 := GlobalTheory.T.card_lPowerTorsion_kernel_eq_lPart_isogenyDegree k l hlK A B f hf
    have e2 := GlobalTheory.T.card_lPowerTorsion_kernel_eq_lPart_isogenyDegree k l hlK A C q hq
    have hset : Nat.card {x : A.Pt // x ≫ f.hom = 1 ∧ ∃ n : ℕ, x ^ l ^ n = 1} =
        Nat.card {x : A.Pt // x ≫ q.hom = 1 ∧ ∃ n : ℕ, x ^ l ^ n = 1} := by
      apply Nat.card_congr
      apply Equiv.subtypeEquivRight
      intro x
      constructor
      · rintro ⟨h1, n, hn⟩
        refine ⟨?_, n, hn⟩
        have hm : x ∈ invKer f := ⟨h1, l ^ n, by push_cast; exact pow_ne_zero _ hlK, hn⟩
        rw [← hker] at hm
        exact hm
      · rintro ⟨h1, n, hn⟩
        refine ⟨?_, n, hn⟩
        rw [← hqh, comp_hom, ← Category.assoc, h1]
        exact (ptMap h).map_one
    rw [e1, e2] at hset
    exact Nat.pow_right_injective hl.two_le hset
  have hd0 : deg f ≠ 0 := by
    intro h0; apply hd; rw [h0]; simp
  have hq0 : deg q ≠ 0 := by
    intro h0; apply hd0; rw [hdeg, h0, zero_mul]
  have hh0 : deg h ≠ 0 := by
    intro h0; apply hd0; rw [hdeg, h0, mul_zero]
  have hh1 : deg h = 1 := by
    rw [Nat.eq_one_iff_not_exists_prime_dvd]
    intro l hl hdvd
    by_cases hlK : (l : k) = 0
    · apply hd
      obtain ⟨c, hc⟩ : l ∣ deg f := hdeg ▸ dvd_mul_of_dvd_right hdvd _
      rw [hc]; push_cast; rw [hlK, zero_mul]
    · haveI := Fact.mk hl
      have e' := hv l hl hlK
      rw [hdeg, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hq0 hh0] at e'
      have h1 := one_le_padicValNat_of_dvd hh0 hdvd
      rw [← Nat.padicValNat_def] at h1
      omega
  have hiso : IsIso h := (GlobalTheory.AV.AbVar.isIso_iff_deg_eq_one k C B h).2 hh1
  obtain ⟨r, hr⟩ := huniv A (e • 𝟙 A) (fun x hx => by
    change x ≫ (e • 𝟙 A).hom = 1
    rw [nsmul_hom, id_hom, GlobalTheory.AV.DegSep.comp_pow_id]
    exact hkill _ x hx.1)
  refine ⟨inv h ≫ r, ?_⟩
  rw [← hqh, Category.assoc, IsIso.hom_inv_id_assoc, hr]

end GlobalTheory.AV.AbVar.KilledInverse

namespace GlobalTheory.AV

theorem exists_comp_eq_pow_of_ker_killed : ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ (l : A ⟶ B), IsMonHom l → ∀ e : ℕ, IsUnit (e : k) → (∀ (T : Over (Sp k)) (x : T ⟶ A), x ≫ l = 1 → x ^ e = 1) → ∃ m : B ⟶ A, IsMonHom m ∧ l ≫ m = 𝟙 A ^ e := by
  intro k _ A B _ _ _ _ g hA hB sA sB l hl e he hkill
  let A' : AbVar k := { X := A, ab := hA, dim := g, smooth := sA }
  let B' : AbVar k := { X := B, ab := hB, dim := g, smooth := sB }
  obtain ⟨m, hm⟩ := AbVar.KilledInverse.exists_comp_eq_nsmul A' B' (AbVar.Hom.mk (A := A') (B := B') l) rfl e he
    (fun T x hx => hkill T x hx)
  refine ⟨m.hom, inferInstance, ?_⟩
  have h2 := congrArg AbVar.Hom.hom hm
  rw [AbVar.comp_hom, AbVar.mk_hom, AbVar.nsmul_hom, AbVar.id_hom] at h2
  exact h2

end GlobalTheory.AV
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeExistsCompEqNsmulOfKernelKilledStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianScheme_exists_comp_eq_nsmul_of_kernel_killed : ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ (l : A ⟶ B), IsMonHom l → ∀ e : ℕ, IsUnit (e : k) → (∀ (T : Over (Sp k)) (x : T ⟶ A), x ≫ l = 1 → x ^ e = 1) → ∃ m : B ⟶ A, IsMonHom m ∧ l ≫ m = 𝟙 A ^ e := by
  first | exact @GlobalTheory.AV.exists_comp_eq_pow_of_ker_killed | exact GlobalTheory.AV.exists_comp_eq_pow_of_ker_killed | (intros; apply GlobalTheory.AV.exists_comp_eq_pow_of_ker_killed <;> assumption)
end
end
