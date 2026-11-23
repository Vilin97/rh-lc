module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.BaseOnto
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsGenericModuliPoint
public import Development.AutomorphicArithmetic.CommutativeAlgebra.IsogenyClassExistsOfQuotient
public import Development.AutomorphicArithmetic.CommutativeAlgebra.LatticeGeneration
public import Development.AutomorphicArithmetic.CommutativeAlgebra.MultiplierIsUnit
public import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientLevelOfLatticeGeneration
public import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientMapComp
public import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientModuliIso
public import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientModuliObjectExists
public import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientUniqueOfComp
public import Development.AutomorphicArithmetic.CommutativeAlgebra.TraceEtaIdentity
public import Development.AutomorphicArithmetic.CommutativeAlgebra.TracePullbackIdentity
public import Development.AutomorphicArithmetic.CommutativeAlgebra.TraceUnitOfPullbackMultiplier
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LiftUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPosOfCoprime
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLevelForgettingFiniteEtaleSurjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyOfFinitePresentationOfIsQProjOver
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.OLevDown
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsEtIdealOfPlace
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtModelForgetFiniteEtale

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

noncomputable section

namespace GlobalTheory.UPel.HT.EtLev.LevForget

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

def forgetMap {b : Base D R} {N' : ℕ} {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b N' s'}
    {o : Obj b N' s} {f : S' ⟶ S} (m : ObjMap o' o f) (N : ℕ) (hd : N ∣ N') (hc : N'.Coprime p) :
    ObjMap (o'.forget N hd hc) (o.forget N hd hc) f :=
  ⟨m.φ, m.φ₂, m.cart, m.sq, m.act, m.pol, fun y => m.eta _⟩

end GlobalTheory.UPel.HT.EtLev.LevForget
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ODownEx

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.O.downEx :
    UpperTheory.Gal.FiniteEtaleModels.O.DownEx := by
  intro p _ D hm _ E _ _ gb w q _ r 𝔴 𝔫 S N₀ κ 𝔟₁ 𝔟₂ X₁ X₂ ε h
  obtain ⟨h3, -, -, -, -⟩ := X₂.lev
  obtain ⟨-, hcq₁, -, -, e₁, he₁⟩ := X₁.lev
  have hd : N₀ ∣ N₀ * κ := dvd_mul_right N₀ κ
  have hne : 𝔟₁ ≠ ⊥ := by
    intro h0
    have hq : ((q : 𝓞 D.F)) ∈ uId D q r := Ideal.subset_span (Set.mem_insert _ _)
    have hmem : ((q : 𝓞 D.F)) ^ e₁ ∈ 𝔟₁ := he₁ (Ideal.pow_mem_pow hq e₁)
    rw [h0, Ideal.mem_bot] at hmem
    have hq0 : ((q : 𝓞 D.F)) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
    exact pow_ne_zero e₁ hq0 hmem
  have hL := UpperTheory.Gal.FiniteEtaleModels.O.levDown q (datAt S.atq S.sp) hm (Ow w) S.b (N₀ * κ) X₁.Y.X X₁.Y.s
    X₁.Y.univ 𝔟₁ 𝔟₂ ε hne h X₁.Y.lv X₁.Y.isLev
  obtain ⟨t, ⟨ht, m, hmt⟩, -⟩ := X₂.Y.rep X₁.Y.X X₁.Y.s (X₁.Y.univ.forget N₀ hd hcq₁)
    (fun y => X₁.Y.lv ((algebraMap (𝓞 D.F) D.O) ε • y)) hL
  obtain ⟨u, ⟨hu, ⟨mu⟩⟩, -⟩ := X₂.M.rep X₁.M.X X₁.M.s (X₁.M.univ.forget N₀ hd hcq₁)
  obtain ⟨hfu, heu, -⟩ := GlobalTheory.T.harrisTaylor_levelForgetting_finite_etale_surjective q (datAt S.atq S.sp) (Ow w) S.b N₀ (N₀ * κ) hd hcq₁ h3
    X₂.M X₁.M u hu ⟨mu⟩
  have hsq : t ≫ X₂.π = X₁.π ≫ u := by
    obtain ⟨v, -, huniq⟩ := X₂.M.rep X₁.Y.X X₁.Y.s (X₁.Y.univ.forget N₀ hd hcq₁)
    have e1 := huniq (t ≫ X₂.π) ⟨by rw [Category.assoc, X₂.ov, ht], ⟨m.comp X₂.mπ⟩⟩
    have e2 := huniq (X₁.π ≫ u)
      ⟨by rw [Category.assoc, hu, X₁.ov], ⟨(LevForget.forgetMap X₁.mπ N₀ hd hcq₁).comp mu⟩⟩
    rw [e1, e2]
  haveI := X₁.fin
  haveI := X₁.et
  haveI := X₂.fin
  haveI := X₂.et
  haveI : IsFinite (t ≫ X₂.π) := by rw [hsq]; infer_instance
  haveI : Etale (t ≫ X₂.π) := by rw [hsq]; infer_instance
  exact ⟨t, m, ht, IsFinite.of_comp t X₂.π, Etale.of_comp t X₂.π, hmt⟩
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.OEpsEx

section

@[expose] public section

theorem UpperTheory.Gal.FiniteEtaleModels.O.epsEx :
    UpperTheory.Gal.FiniteEtaleModels.O.EpsEx := by
  intro A _ _ _ 𝔟₁ 𝔟₂ a₁ a₂ M₁ M₂ t hpos hM hle h₁ h₂
  unfold UpperTheory.Gal.Int.Geo.IsGen at h₁ h₂
  have hM1 : (M₁ : A) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  have hMc : (M₁ : A) = (t : A) * (M₂ : A) := by rw [hM]; push_cast; ring
  set I₁ := Ideal.span {a₁} ⊔ Ideal.span {(M₁ : A)} with hI₁
  have hI₁0 : I₁ ≠ ⊥ := by
    intro h
    have hmem : (M₁ : A) ∈ I₁ := Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    rw [h, Ideal.mem_bot] at hmem
    exact hM1 hmem
  have h𝔟0 : 𝔟₁ ≠ ⊥ := by
    intro h
    rw [h, Ideal.mul_bot, eq_comm, Ideal.span_singleton_eq_bot] at h₁
    exact hM1 h₁
  have hkey : ∀ {J : Ideal A}, J * 𝔟₂ ≤ Ideal.span {(M₁ : A)} → J ≤ I₁ := by
    intro J hJ
    have h3 : J * 𝔟₁ ≤ I₁ * 𝔟₁ := by
      rw [h₁]
      exact le_trans (Ideal.mul_mono_right hle) hJ
    rw [← Ideal.dvd_iff_le] at h3 ⊢
    exact (mul_dvd_mul_iff_right h𝔟0).mp h3
  have hta : (t : A) * a₂ ∈ I₁ := by
    have hsp : Ideal.span {(t : A) * a₂} ≤ I₁ := by
      apply hkey
      rw [← Ideal.span_singleton_mul_span_singleton, mul_assoc, hMc,
        ← Ideal.span_singleton_mul_span_singleton, ← h₂]
      exact Ideal.mul_mono_right (Ideal.mul_mono_left le_sup_left)
    exact hsp (Ideal.mem_span_singleton_self _)
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hta
  obtain ⟨ε, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hz
  refine ⟨ε, ⟨-d, by rw [← hyz]; ring⟩, ?_⟩
  have hJK : I₁ * Ideal.span {ε} ⊔ Ideal.span {(M₁ : A)} =
      Ideal.span {(t : A)} * (Ideal.span {a₂} ⊔ Ideal.span {(M₂ : A)}) := by
    rw [Ideal.mul_sup, Ideal.span_singleton_mul_span_singleton,
      Ideal.span_singleton_mul_span_singleton, ← hMc, hI₁, Ideal.sup_mul,
      Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton]
    apply le_antisymm
    · refine sup_le (sup_le ?_ ?_) le_sup_right
      · rw [Ideal.span_singleton_le_iff_mem]
        have hae : a₁ * ε = (t : A) * a₂ - d * M₁ := by rw [← hyz]; ring
        rw [hae]
        exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
          (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
      · rw [Ideal.span_singleton_le_iff_mem]
        exact Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    · refine sup_le ?_ le_sup_right
      rw [Ideal.span_singleton_le_iff_mem, ← hyz]
      refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_sup_left ?_))
        (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
      rw [mul_comm]
      exact Ideal.mem_span_singleton_self _
  apply mul_left_cancel₀ hI₁0
  rw [h₁, ← mul_assoc, Ideal.mul_sup, h₁, hJK, mul_assoc, h₂,
    Ideal.span_singleton_mul_span_singleton, ← hMc]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.OStepF

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.FiniteEtaleModels.O


private theorem stepF_of (hGen : GenEx) (hComp : QComp) (hIso : QIso) (hCls : ClsEx) (hEta : TrEta) (hUnit : TrUnit)
    (hEps : EpsEx) (hDown : DownEx) : UpperTheory.Gal.FiniteEtaleModels.StepF := by
  intro p _ D G L hSc E _ _ gb w q _ r 𝔴 𝔫 S k T N₀ κ 𝔟₁ 𝔟₂ X₁ X₂ hle M₁ M₂ c₁ c₂ a₁ a₂ hN₁ hN₂ hM C₁ C₂ W
  obtain ⟨hM₁, hg₁⟩ := hN₁
  obtain ⟨hM₂, hg₂⟩ := hN₂
  obtain ⟨t, ht⟩ := hM
  have hM₁' : (M₁ : ℕ) = N₀ * κ * c₁ := hM₁
  have hM₂' : (M₂ : ℕ) = N₀ * c₂ := hM₂
  have hpos : 0 < (M₁ : ℕ) := by have := M₁.2.1; omega
  obtain ⟨h3, hcq₂, -, -, -⟩ := X₂.lev
  obtain ⟨-, hcq₁, -, -, -⟩ := X₁.lev
  have hN₀pos : 0 < N₀ := by omega
  have hd : N₀ ∣ N₀ * κ := dvd_mul_right N₀ κ
  obtain ⟨ε, hdvd, hεid⟩ := hEps (𝓞 D.F) 𝔟₁ 𝔟₂ a₁ a₂ M₁ M₂ t hpos ht hle hg₁ hg₂
  obtain ⟨τ, m, hτ, hfin, het, hml⟩ :=
    hDown p D hSc.m1 hSc.a1 E gb w q r 𝔴 𝔫 S N₀ κ 𝔟₁ 𝔟₂ X₁ X₂ ε hεid
  have hcart : IsGrpPullback (T.M M₁).univ.A (X₁.Y.univ.forget N₀ hd hcq₁).A C₁.j C₁.m.φ := C₁.m.cart
  have hsq : Geo.Tor.IsSquare C₁.m.φ C₁.m.φ₂ := C₁.m.sq
  have hact : ∀ x, Over.Hom.left ((T.M M₁).univ.act.act x) ≫ C₁.m.φ =
      C₁.m.φ ≫ Over.Hom.left ((X₁.Y.univ.forget N₀ hd hcq₁).act.act x) := C₁.m.act
  have hpol : LBIso (T.M M₁).univ.P ((X₁.Y.univ.forget N₀ hd hcq₁).P.pull C₁.m.φ₂) := C₁.m.pol
  have heF : ∀ y : D.La, Over.Hom.left ((T.M M₁).univ.eta ((c₁ * κ) • y)) ≫ C₁.m.φ =
      C₁.j ≫ Over.Hom.left ((X₁.Y.univ.forget N₀ hd hcq₁).eta y) := by
    intro y
    rw [Obj.forget_eta, Nat.mul_div_cancel_left κ hN₀pos, mul_smul]
    exact C₁.m.eta (κ • y)
  obtain ⟨nF, hnFφ⟩ : ∃ n : @QMap q _ (datAt S.atq S.sp) (Ow w) E _ _ _ S.b gb _ _ X₁.Y.s (T.M M₁).s _ _
      (T.M M₁).univ (X₁.Y.univ.forget N₀ hd hcq₁) C₁.j (c₁ * κ), n.φ = C₁.m.φ :=
    ⟨⟨C₁.m.φ, C₁.m.φ₂, hcart, hsq, hact, hpol, heF⟩, rfl⟩
  obtain ⟨nA, hnA⟩ := (hComp q (datAt S.atq S.sp) (Ow w) E S.b gb (M₁ : ℕ) N₀ (c₁ * κ) (T.M M₁).X X₁.Y.X
    X₂.Y.X (T.M M₁).s X₁.Y.s X₂.Y.s (T.M M₁).univ (X₁.Y.univ.forget N₀ hd hcq₁) X₂.Y.univ C₁.j τ).1 nF m
  obtain ⟨n₂, hn₂⟩ := (hComp q (datAt S.atq S.sp) (Ow w) E S.b gb (M₂ : ℕ) N₀ c₂ (T.M M₂).X X₂.Y.X
    X₂.Y.X (T.M M₂).s X₂.Y.s X₂.Y.s (T.M M₂).univ X₂.Y.univ X₂.Y.univ C₂.j (𝟙 _)).2.2.2
    (T.M M₁).X (T.M M₁).s W.o W.π W.φ C₂.m
  obtain ⟨hiso, hpol'⟩ :=
    hUnit p D G L E gb 1 (T.M M₁).X (T.M M₁).s M₁ M₂ (T.M M₁).univ W.o W.ψ W.trans (one_mem _)
  have hex : ∀ (n : ℕ) (x : D.La), ∃ v ∈ LaHat D, (L.actG 1) (inAf D x) = inAf D x + n • v :=
    fun n x => ⟨0, zero_mem _, by simp⟩
  have heta₁ : ∀ y : D.La, (T.M M₁).univ.eta ((c₁ * κ) • y) ≫ W.ψ = W.o.eta (c₂ • y) :=
    fun y => hEta p D G L E gb 1 (T.M M₁).X (T.M M₁).s M₁ M₂ (T.M M₁).univ W.o W.ψ W.trans N₀ (c₁ * κ) c₂
      (by rw [hM₁']; ring) hM₂' y y (hex N₀ y)
  obtain ⟨nB, hnB⟩ := hIso q (datAt S.atq S.sp) (Ow w) E S.b gb (M₂ : ℕ) (M₁ : ℕ) N₀ c₂ (c₁ * κ) (T.M M₁).X
    X₂.Y.X (T.M M₁).s X₂.Y.s (T.M M₁).univ W.o X₂.Y.univ (W.π ≫ C₂.j) W.ψ hiso W.trans.1 W.trans.2.1 hpol'
    heta₁ n₂
  have heq : ∀ y : D.La, (T.M M₁).univ.eta ((algebraMap (𝓞 D.F) D.O) ((t : 𝓞 D.F) * a₂) • y) =
      (T.M M₁).univ.eta ((algebraMap (𝓞 D.F) D.O) (a₁ * ε) • y) := by
    intro y
    obtain ⟨z, hz⟩ := hdvd
    have e1 : (algebraMap (𝓞 D.F) D.O) (a₁ * ε) • y = (algebraMap (𝓞 D.F) D.O) ((t : 𝓞 D.F) * a₂) • y +
        (M₁ : ℕ) • ((algebraMap (𝓞 D.F) D.O) z • y) := by
      have h' : a₁ * ε = (t : 𝓞 D.F) * a₂ + ((M₁ : ℕ) : 𝓞 D.F) * z := by linear_combination hz
      rw [h', map_add (f := _), add_smul, map_mul (algebraMap (𝓞 D.F) D.O) ((M₁ : ℕ) : 𝓞 D.F) z, mul_smul,
        map_natCast, Nat.cast_smul_eq_nsmul]
    have h1 := (T.M M₁).univ.eta_add ((algebraMap (𝓞 D.F) D.O) ((t : 𝓞 D.F) * a₂) • y)
      ((M₁ : ℕ) • ((algebraMap (𝓞 D.F) D.O) z • y))
    have h2 := (T.M M₁).univ.eta_ker ((algebraMap (𝓞 D.F) D.O) z • y)
    rw [e1]
    refine (h1.trans ?_).symm
    exact (congrArg (_ * ·) h2).trans (_root_.mul_one _)
  have hkey : ∀ y : D.La, (T.M M₁).univ.eta ((algebraMap (𝓞 D.F) D.O) ((t : 𝓞 D.F) * a₂) • y) ≫ W.ψ =
      W.o.eta ((algebraMap (𝓞 D.F) D.O) a₂ • y) := by
    intro y
    have h' := hEta p D G L E gb 1 (T.M M₁).X (T.M M₁).s M₁ M₂ (T.M M₁).univ W.o W.ψ W.trans M₂ t 1 ht
      (_root_.mul_one _).symm ((algebraMap (𝓞 D.F) D.O) a₂ • y) ((algebraMap (𝓞 D.F) D.O) a₂ • y) (hex _ _)
    rw [map_mul, mul_smul, map_natCast, Nat.cast_smul_eq_nsmul, h', one_smul]
  have lvA : ∀ y : D.La, Over.Hom.left ((T.M M₁).univ.eta ((algebraMap (𝓞 D.F) D.O) ((t : 𝓞 D.F) * a₂) • y)) ≫ nA.φ =
      (C₁.j ≫ τ) ≫ Over.Hom.left (X₂.Y.lv y) := by
    intro y
    rw [heq, hnA, hnFφ, map_mul, mul_smul]
    exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ m.φ) (C₁.lv _))).trans
      ((Category.assoc _ _ _).trans ((congrArg (C₁.j ≫ ·) (hml y)).trans (Category.assoc _ _ _).symm))
  have lvB : ∀ y : D.La, Over.Hom.left ((T.M M₁).univ.eta ((algebraMap (𝓞 D.F) D.O) ((t : 𝓞 D.F) * a₂) • y)) ≫ nB.φ =
      (W.π ≫ C₂.j) ≫ Over.Hom.left (X₂.Y.lv y) := by
    intro y
    rw [hnB, hn₂, ← Category.assoc, ← Over.comp_left, hkey, ← Category.assoc]
    exact (congrArg (· ≫ C₂.m.φ) (W.φ.eta _)).trans ((Category.assoc _ _ _).trans
      ((congrArg (W.π ≫ ·) (C₂.lv y)).trans (Category.assoc _ _ _).symm))
  obtain ⟨CA, hCAj, hCAm⟩ : ∃ C : @Cls q _ (datAt S.atq S.sp) (Ow w) E _ _ _ S.b gb (T.M M₁).X (T.M M₁).s
      (M₁ : ℕ) N₀ 𝔟₂ X₂.Y (algebraMap (Ow w) E) (T.M M₁).univ (c₁ * κ) ((t : 𝓞 D.F) * a₂),
      C.j = C₁.j ≫ τ ∧ C.m.φ = nA.φ :=
    ⟨⟨C₁.j ≫ τ, (Category.assoc _ _ _).trans ((congrArg (C₁.j ≫ ·) hτ).trans C₁.ov), nA, lvA⟩, rfl, rfl⟩
  obtain ⟨CB, hCBj, hCBm⟩ : ∃ C : @Cls q _ (datAt S.atq S.sp) (Ow w) E _ _ _ S.b gb (T.M M₁).X (T.M M₁).s
      (M₁ : ℕ) N₀ 𝔟₂ X₂.Y (algebraMap (Ow w) E) (T.M M₁).univ (c₁ * κ) ((t : 𝓞 D.F) * a₂),
      C.j = W.π ≫ C₂.j ∧ C.m.φ = nB.φ :=
    ⟨⟨W.π ≫ C₂.j, (Category.assoc _ _ _).trans ((congrArg (W.π ≫ ·) C₂.ov).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ spMap _) W.ov))), nB, lvB⟩, rfl, rfl⟩
  have hgen : IsGen ((t : 𝓞 D.F) * a₂) (M₁ : ℕ) 𝔟₂ := by
    rw [ht]
    exact (hGen (𝓞 D.F) 𝔟₂ M₂ (by have := M₂.2.1; omega)).2 a₂ t hg₂
  obtain ⟨hj, hφ⟩ := (hCls q (datAt S.atq S.sp) (Ow w) E S.b gb (algebraMap (Ow w) E) S.mat (M₁ : ℕ) N₀
    (c₁ * κ) ((t : 𝓞 D.F) * a₂) 𝔟₂ (by rw [hM₁']; ring) hpos h3 hcq₂ hgen X₂.Y (T.M M₁).X (T.M M₁).s
    (T.M M₁).univ).2 CA CB
  rw [hCAj, hCBj] at hj
  rw [hCAm, hCBm, hnA, hnB, hn₂, hnFφ] at hφ
  exact ⟨⟨τ, hτ, m.φ, m.cart.1.w⟩, ⟨hj, hφ⟩, hfin, het, m.cart.1⟩

theorem stepF : UpperTheory.Gal.FiniteEtaleModels.StepF :=
  stepF_of UpperTheory.exists_generic_moduli_point UpperTheory.quotient_map_comp UpperTheory.quotient_moduli_iso
    (UpperTheory.isogeny_class_exists_of_quotient UpperTheory.quotient_moduli_object_exists UpperTheory.quotient_map_comp (UpperTheory.quotient_unique_of_comp UpperTheory.quotient_map_comp) (UpperTheory.quotient_level_of_lattice_generation UpperTheory.lattice_generation))
    UpperTheory.trace_eta_identity (UpperTheory.trace_unit_of_pullback_multiplier UpperTheory.trace_pullback_identity UpperTheory.multiplier_is_unit) epsEx downEx

end UpperTheory.Gal.FiniteEtaleModels.O
end
end
end
