module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeformationBaseRingLocalDomainStatement
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFamilyFromVeryDensePoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueSectionOfDense
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelEndomorphismsSpreadOverBasicOpen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPtOfThetaConstantsAndFirstJetsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyValueTwoFibresLocalRingStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFamilyLocalDomainOfTwoFibres

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MBLow.TwoFibres

open GlobalTheory.ZM

theorem unitS_spMap_eq {o R : Type} [CommRing o] [CommRing R] (β : o →+* R) (u : oˣ) :
    unitS (spMap β) u = unitOn (Units.map β.toMonoidHom u) := by
  apply Units.ext
  exact (congrArg (fun q => q.hom (u : o)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm

theorem unitS_spMap_comp {o R R' : Type} [CommRing o] [CommRing R] [CommRing R'] (β : o →+* R) (i : R →+* R')
    (u : oˣ) : unitS (spMap i ≫ spMap β) u = unitOn (Units.map (i.comp β).toMonoidHom u) := by
  rw [SpreadLevel.unitS_comp, unitS_spMap_eq β]
  exact (unitS_spMap_eq i _).trans (congrArg unitOn (Units.ext rfl))

def ofLevel {o : Type} [CommRing o] {g k : ℕ} (hk : 0 < k) (b : TBase o k) {K : Type} [Field K] [IsAlgClosed K]
    (s : Sp K ⟶ Sp o) (P : PolAV (Sp K)) (hg : P.g = g) {ze : Γ(Sp K, ⊤)ˣ} (l : Level P k ze)
    (hze : ze = unitS s b.ζ) : TObj g k PEmpty b s where
  A := P.A
  ab := P.isAb
  dim := hg ▸ P.smoothDim
  L := P.L
  isLB := P.isLB
  rigid := P.rigid
  sym := P.sym
  ample := P.ample
  ktriv := P.ktriv
  pt := levelBasis l hg
  torsion := fun i => l.torsion _
  bij := by
    intro K' _ _ x y hy
    subst hg
    haveI : NeZero k := ⟨hk.ne'⟩
    obtain ⟨c, hc⟩ := l.span K' x y hy
    refine ⟨fun i => ((c i : ℕ) : ZMod k), ?_, fun c' hc' => ?_⟩
    · simp only [levelBasis_rfl, ZMod.val_natCast, Nat.mod_eq_of_lt (c _).2]
      exact hc
    · have e := l.indep K' x (fun i => ⟨(c' i).val, ZMod.val_lt _⟩) c (hc'.trans hc.symm)
      funext i
      have := congrArg (fun d => ((d i : ℕ) : ZMod k)) e
      simpa using this
  pairing := by
    intro i j
    subst hg hze
    exact l.pairing i j
  act := fun e => e.elim
  hom := fun e => e.elim

theorem ofLevel_lab {o : Type} [CommRing o] {g k : ℕ} (hk : 0 < k) (b : TBase o k) {K : Type} [Field K]
    [IsAlgClosed K] (s : Sp K ⟶ Sp o) (P : PolAV (Sp K)) (hg : P.g = g) {ze : Γ(Sp K, ⊤)ˣ} (l : Level P k ze)
    (hze : ze = unitS s b.ζ) (a : Ix g k) : (ofLevel hk b s P hg l hze).lab a = levelPoint l hg a := by
  subst hg
  rfl

theorem ofLevel_hasTh {o : Type} [CommRing o] {g k : ℕ} (hk : 0 < k ^ 2) (b : TBase o (k ^ 2)) {K : Type} [Field K]
    [IsAlgClosed K] (s : Sp K ⟶ Sp o) (P : PolAV (Sp K)) (hg : P.g = g) {ze : Γ(Sp K, ⊤)ˣ}
    (l : Level P (k ^ 2) ze) (hze : ze = unitS s b.ζ) (w : Ix g (k ^ 2) → K)
    (h : IsThetaPt P k (levelPoint l hg) fun a => Ex.fnOf (w a)) :
    (ofLevel hk b s P hg l hze).HasTh (𝟙 _) w := by
  have hx : (fun a => (Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) ≫
      (ofLevel hk b s P hg l hze).lab a) = levelPoint l hg := by
    funext a
    have e : (Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) = 𝟙 _ := by
      ext; rfl
    rw [e, Category.id_comp, ofLevel_lab]
  subst hg
  exact (congrArg (fun x => IsThetaPt P k x (fun a => Ex.fnOf (w a))) hx).mpr h

theorem linComb_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {m : ℕ} (x' : Fin m → (Out.baseOver S' ⟶ G'))
    (x : Fin m → (Out.baseOver S ⟶ G)) (hx : ∀ i, (x' i).left ≫ φ = f ≫ (x i).left) (c : Fin m → ℕ) :
    (Out.linComb x' c).left ≫ φ = f ≫ (Out.linComb x c).left := by
  let U : Over.mk ((Out.baseOver S').hom ≫ f) ⟶ Out.baseOver S := Over.homMk f (by simp)
  have e : ∀ i, pushHom h (Out.baseOver S') (x' i) = preHom U (x i) := fun i =>
    Over.OverMorphism.ext (hx i)
  have := congrArg (fun z => z.left) ((SpreadLevel.map_linComb (pushHom h (Out.baseOver S')) x' c).trans
    ((congrArg (fun z => Out.linComb z c) (funext e)).trans (SpreadLevel.map_linComb (preHom U) x c).symm))
  exact this

end GlobalTheory.MBLow.TwoFibres

namespace GlobalTheory.MBLow

open GlobalTheory.ZM GlobalTheory.MBLow.TwoFibres

theorem exists_family_of_two_fibres : ∀ g n : ℕ, n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [Field o] [CharZero o] (ζ : oˣ) (W : Type) [CommRing W] [IsDomain W] [IsNoetherianRing W] [IsLocalRing W] (β : o →+* W) (v : (Fin (2 * g) → ZMod ((n ^ j) ^ 2)) → W) (K₀ K₁ : Type) [Field K₀] [IsAlgClosed K₀] [Field K₁] [IsAlgClosed K₁] (i₀ : W →+* K₀) (i₁ : W →+* K₁), (∀ q : Ideal W, q.IsPrime → q = RingHom.ker i₀ ∨ q = RingHom.ker i₁) → ∀ (P₀ : PolAV (Sp K₀)) (P₁ : PolAV (Sp K₁)) (h₀ : P₀.g = g) (h₁ : P₁.g = g) (l₀ : Out.Level P₀ ((n ^ j) ^ 2) (unitOn (Units.map (i₀.comp β).toMonoidHom ζ))) (l₁ : Out.Level P₁ ((n ^ j) ^ 2) (unitOn (Units.map (i₁.comp β).toMonoidHom ζ))), (IsThetaPt P₀ (n ^ j) (levelPoint l₀ h₀) fun a => fnOf (i₀ (v a))) → (IsThetaPt P₁ (n ^ j) (levelPoint l₁ h₁) fun a => fnOf (i₁ (v a))) → ∃ (P : PolAV (Sp W)) (pt : (Fin (2 * g) → ZMod ((n ^ j) ^ 2)) → (baseOver (Sp W) ⟶ P.A)) (φ₀ : P₀.A.left ⟶ P.A.left) (φ₁ : P₁.A.left ⟶ P.A.left), P.g = g ∧ (∀ a, pt a ^ ((n ^ j) ^ 2) = 1) ∧ IsGrpPullback P₀.A P.A (spMap i₀) φ₀ ∧ IsGrpPullback P₁.A P.A (spMap i₁) φ₁ ∧ LBIso P₀.L (P.L.pull φ₀) ∧ LBIso P₁.L (P.L.pull φ₁) ∧ (∀ a, (levelPoint l₀ h₀ a).left ≫ φ₀ = spMap i₀ ≫ (pt a).left) ∧ ∀ a, (levelPoint l₁ h₁ a).left ≫ φ₁ = spMap i₁ ≫ (pt a).left := by
  intro g n hn hodd
  obtain ⟨hL, hL2⟩ := abelianSchemeLaws_all
  obtain ⟨j₀, H⟩ := exists_tObj_of_veryDense hL hL2 g PEmpty (fun e => e.elim) 0 n hn hodd
  refine ⟨j₀, fun j hj o _ _ ζ W _ _ _ _ β v K₀ K₁ _ _ _ _ i₀ i₁ hW P₀ P₁ h₀ h₁ l₀ l₁ hT₀ hT₁ => ?_⟩
  have hk : 0 < (n ^ j) ^ 2 := pow_pos (pow_pos hn.pos _) _
  have hζ : IsPrimitiveRoot ζ ((n ^ j) ^ 2) := by
    refine IsPrimitiveRoot.of_map_of_injective (f := (Units.map (Scheme.ΓSpecIso (CommRingCat.of K₀)).inv.hom.toMonoidHom).comp
      (Units.map (i₀.comp β).toMonoidHom)) l₀.prim ?_
    exact (Units.map_injective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K₀)).inv).1).comp
      (Units.map_injective (i₀.comp β).injective)
  let b : TBase o ((n ^ j) ^ 2) :=
    { ζ := ζ
      unit := (Nat.cast_ne_zero.2 hk.ne').isUnit
      prim := fun K _ β' => (IsPrimitiveRoot.coe_units_iff.2 hζ).map_of_injective β'.injective }
  let t₀ := ofLevel hk b (spMap i₀ ≫ spMap β) P₀ h₀ l₀ (unitS_spMap_comp β i₀ ζ).symm
  let t₁ := ofLevel hk b (spMap i₁ ≫ spMap β) P₁ h₁ l₁ (unitS_spMap_comp β i₁ ζ).symm
  have hS₀ : t₀.Shape (fun e => e.elim) 0 := fun e => e.elim
  have hS₁ : t₁.Shape (fun e => e.elim) 0 := fun e => e.elim
  have hh₀ : t₀.HasTh (𝟙 _) (fun a => i₀ (v a)) :=
    ofLevel_hasTh hk b _ P₀ h₀ l₀ (unitS_spMap_comp β i₀ ζ).symm _ hT₀
  have hh₁ : t₁.HasTh (𝟙 _) (fun a => i₁ (v a)) :=
    ofLevel_hasTh hk b _ P₁ h₁ l₁ (unitS_spMap_comp β i₁ ζ).symm _ hT₁
  have hvd : VeryDense (objPrimes b (fun e : PEmpty => e.elim) 0 β v) := by
    intro q f hq hf
    rcases hW q hq with rfl | rfl
    · exact ⟨_, ⟨K₀, inferInstance, inferInstance, i₀, t₀, rfl, hS₀, hh₀⟩, hq, le_rfl, hf⟩
    · exact ⟨_, ⟨K₁, inferInstance, inferInstance, i₁, t₁, rfl, hS₁, hh₁⟩, hq, le_rfl, hf⟩
  obtain ⟨t, -, ht⟩ := H j hj o b W β v hvd
  obtain ⟨φ₀, hp₀, hL₀, hpt₀, -⟩ := ht K₀ i₀ t₀ hS₀ hh₀
  obtain ⟨φ₁, hp₁, hL₁, hpt₁, -⟩ := ht K₁ i₁ t₁ hS₁ hh₁
  haveI := t.ab.comm
  refine ⟨t.pol, t.lab, φ₀, φ₁, rfl, fun a => DenseBasis.linComb_pow_eq_one t.pt t.torsion _, hp₀, hp₁, hL₀, hL₁,
    fun a => ?_, fun a => ?_⟩
  · rw [← ofLevel_lab hk b (spMap i₀ ≫ spMap β) P₀ h₀ l₀ (unitS_spMap_comp β i₀ ζ).symm a]
    exact linComb_push hp₀ t₀.pt t.pt hpt₀ _
  · rw [← ofLevel_lab hk b (spMap i₁ ≫ spMap β) P₁ h₁ l₁ (unitS_spMap_comp β i₁ ζ).symm a]
    exact linComb_push hp₁ t₁.pt t.pt hpt₁ _

end GlobalTheory.MBLow
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFamilyLocalDomainOfTwoFibresStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_family_localDomain_of_twoFibres : ∀ g n : ℕ, n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [Field o] [CharZero o] (ζ : oˣ) (W : Type) [CommRing W] [IsDomain W] [IsNoetherianRing W] [IsLocalRing W] (β : o →+* W) (v : (Fin (2 * g) → ZMod ((n ^ j) ^ 2)) → W) (K₀ K₁ : Type) [Field K₀] [IsAlgClosed K₀] [Field K₁] [IsAlgClosed K₁] (i₀ : W →+* K₀) (i₁ : W →+* K₁), (∀ q : Ideal W, q.IsPrime → q = RingHom.ker i₀ ∨ q = RingHom.ker i₁) → ∀ (P₀ : PolAV (Sp K₀)) (P₁ : PolAV (Sp K₁)) (h₀ : P₀.g = g) (h₁ : P₁.g = g) (l₀ : Out.Level P₀ ((n ^ j) ^ 2) (unitOn (Units.map (i₀.comp β).toMonoidHom ζ))) (l₁ : Out.Level P₁ ((n ^ j) ^ 2) (unitOn (Units.map (i₁.comp β).toMonoidHom ζ))), (IsThetaPt P₀ (n ^ j) (levelPoint l₀ h₀) fun a => fnOf (i₀ (v a))) → (IsThetaPt P₁ (n ^ j) (levelPoint l₁ h₁) fun a => fnOf (i₁ (v a))) → ∃ (P : PolAV (Sp W)) (pt : (Fin (2 * g) → ZMod ((n ^ j) ^ 2)) → (baseOver (Sp W) ⟶ P.A)) (φ₀ : P₀.A.left ⟶ P.A.left) (φ₁ : P₁.A.left ⟶ P.A.left), P.g = g ∧ (∀ a, pt a ^ ((n ^ j) ^ 2) = 1) ∧ IsGrpPullback P₀.A P.A (spMap i₀) φ₀ ∧ IsGrpPullback P₁.A P.A (spMap i₁) φ₁ ∧ LBIso P₀.L (P.L.pull φ₀) ∧ LBIso P₁.L (P.L.pull φ₁) ∧ (∀ a, (levelPoint l₀ h₀ a).left ≫ φ₀ = spMap i₀ ≫ (pt a).left) ∧ ∀ a, (levelPoint l₁ h₁ a).left ≫ φ₁ = spMap i₁ ≫ (pt a).left := by
  first | exact @GlobalTheory.MBLow.exists_family_of_two_fibres | exact GlobalTheory.MBLow.exists_family_of_two_fibres | (intros; apply GlobalTheory.MBLow.exists_family_of_two_fibres <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyRuleConstantAlongDeformationOfClauses

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow.KeyTop

theorem levelPoint_cast {S : Scheme.{0}} {P : PolAV S} {M : ℕ} {u₁ u₂ : Γ(S, ⊤)ˣ} (h : u₁ = u₂)
    (l : Out.Level P M u₁) {g : ℕ} (hg : P.g = g) : levelPoint (h ▸ l) hg = levelPoint l hg := by
  subst h; rfl

theorem exhaust {K : Type} [Field K] [IsAlgClosed K] {P : PolAV (Sp K)} {M : ℕ} {ze : Γ(Sp K, ⊤)ˣ}
    (lev : Out.Level P M ze) {g : ℕ} (hg : P.g = g) (z : baseOver (Sp K) ⟶ P.A) (hz : z ^ M = 1) :
    ∃ a, levelPoint lev hg a = z := by
  subst hg
  obtain ⟨c, hc⟩ := lev.span K (𝟙 _) z hz
  refine ⟨fun i => ((c i : ℕ) : ZMod M), ?_⟩
  rw [levelPoint_rfl, Out.Level.toPt, ← hc]
  congr 1
  funext i; exact ZMod.val_cast_of_lt (c i).isLt

end GlobalTheory.MBLow.KeyTop

namespace GlobalTheory.MBLow.KeyTop

theorem transfer_of_rule4 : ∀ κ : Rule, Rule4 κ → Transfer κ := by
  intro κ hκ g n hn hodd
  obtain ⟨j₁, hj₁⟩ := GlobalTheory.T.exists_family_localDomain_of_twoFibres g n hn hodd
  refine ⟨max j₁ 1, fun j hj C _ _ _ _ _ e x hg ζ lev k hD => ?_⟩
  have hj1 : j₁ ≤ j := le_trans (le_max_left _ _) hj
  have hj2 : 1 ≤ j := le_trans (le_max_right _ _) hj
  have hmodd : Odd (n ^ j) := hodd.pow
  have hm3 : 3 ≤ n ^ j := by
    have h2 := hn.two_le
    have hne : n ≠ 2 := fun h => by subst h; exact (Nat.not_even_iff_odd.mpr hodd) even_two
    have := Nat.le_self_pow (show j ≠ 0 by omega) n
    omega
  obtain ⟨Θ, Γ, π, b, hπ, hb, hJ, ε, hε, hD'⟩ := hD
  haveI : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)⟩
  let Φ : (Fin (2 * g) → ZMod ((n ^ j) ^ 2)) ⊕ (Fin (2 * g) → ZMod ((n ^ j) ^ 2)) × Fin g → PowerSeries C :=
    Sum.elim Θ (fun p => Γ p.1 p.2)
  let c : Fin 2 → C := ![(ζ : C), k]
  have hbΦ : ∀ a n, ‖PowerSeries.coeff n (Φ a)‖ ≤ b := by
    rintro (a | ⟨a, i⟩) n
    · exact (hb a n).1
    · exact (hb a n).2 i
  have hsΦ : ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε → ∀ a, Summable fun n => ‖e (PowerSeries.coeff n (Φ a)) * u ^ n‖ := by
    intro u hu hu'
    obtain ⟨hs, -⟩ := hD' u hu hu'
    rintro (a | ⟨a, i⟩)
    · exact (hs a).1
    · exact (hs a).2 i
  obtain ⟨u, o, _, _, jo, c₀, hu0, huε, hc₀, W, _, _, _, _, _, _, β, i₀, i₁, φ, hinj, h0, h1, hunit, hprime, hφ⟩ :=
    GlobalTheory.T.exists_deformation_base_ring_local_domain C e _ (Fin 2) Φ c π b ε hπ hε hbΦ hsΦ
  obtain ⟨-, x₀, hg₀, lev₀, hJ₀, hκ₀⟩ := hD' u hu0 huε
  have hc0 : jo (c₀ 0) = ζ := hc₀ 0
  have hc1 : jo (c₀ 1) = k := hc₀ 1
  have hζ0 : c₀ 0 ≠ 0 := fun h => ζ.ne_zero (by rw [← hc0, h, map_zero])
  let ζ₀ : oˣ := Units.mk0 (c₀ 0) hζ0
  have hu₁ : Units.map (i₁.comp β).toMonoidHom ζ₀ = ζ := Units.ext (by
    show (i₁.comp β) (c₀ 0) = ζ
    rw [h1, hc0])
  have hu₀ : Units.map (i₀.comp β).toMonoidHom ζ₀ = Units.map e.toMonoidHom ζ := Units.ext (by
    show (i₀.comp β) (c₀ 0) = e ζ
    rw [h0, RingHom.comp_apply, hc0])
  have hl₀ := (congrArg unitOn hu₀).symm
  have hl₁ := (congrArg unitOn hu₁).symm
  let l₀ := hl₀ ▸ lev₀
  let l₁ := hl₁ ▸ lev
  have eϑ₀ : (fun a => ∑' n, e (PowerSeries.coeff n (Θ a)) * u ^ n) = fun a => i₀ (φ (Sum.inl a)) :=
    funext fun a => ((hφ (Sum.inl a)).1).symm
  have eJ₀ : (fun a i => ∑' n, e (PowerSeries.coeff n (Γ a i)) * u ^ n) = fun a i => i₀ (φ (Sum.inr (a, i))) :=
    funext fun a => funext fun i => ((hφ (Sum.inr (a, i))).1).symm
  have eϑ₁ : (fun a => ∑' n, PowerSeries.coeff n (Θ a) * π ^ n) = fun a => i₁ (φ (Sum.inl a)) :=
    funext fun a => ((hφ (Sum.inl a)).2).symm
  have eJ₁ : (fun a i => ∑' n, PowerSeries.coeff n (Γ a i) * π ^ n) = fun a i => i₁ (φ (Sum.inr (a, i))) :=
    funext fun a => funext fun i => ((hφ (Sum.inr (a, i))).2).symm
  rw [eϑ₀, eJ₀, ← levelPoint_cast hl₀ lev₀ hg₀] at hJ₀
  rw [eϑ₁, eJ₁, ← levelPoint_cast hl₁ lev hg] at hJ
  have hθ₀ := GlobalTheory.T.isThetaPt_of_thetaConstantsAndFirstJets ℂ x₀ g hg₀ (n ^ j) hmodd (by exact_mod_cast pow_ne_zero _ hn.ne_zero) _ _ _ _ hJ₀
  have hθ₁ := GlobalTheory.T.isThetaPt_of_thetaConstantsAndFirstJets C x g hg (n ^ j) hmodd (by exact_mod_cast pow_ne_zero _ hn.ne_zero) _ _ _ _ hJ
  obtain ⟨P, pt, φ₀, φ₁, hPg, hpt, hpb₀, hpb₁, hL₀, hL₁, hc₀', hc₁'⟩ :=
    hj₁ j hj1 o ζ₀ W β (fun a => φ (Sum.inl a)) ℂ C i₀ i₁ hprime x₀.P x.P hg₀ hg l₀ l₁ hθ₀ hθ₁
  have hk₀ : (κ ℂ x₀ : ℂ) = i₀ (β (c₀ 1)) := by
    rw [hκ₀, ← RingHom.comp_apply i₀ β, h0, RingHom.comp_apply, hc1]
  have := GlobalTheory.T.thetaKeyValue_two_fibres_local_ring κ hκ W ℂ C i₀ i₁ hinj hunit P x₀ x g hg₀ hg (n ^ j) hPg hmodd hm3 _ pt
    (levelPoint l₀ hg₀) (levelPoint l₁ hg) φ₀ φ₁ hpt hpb₀ hpb₁ hL₀ hL₁ hc₀' hc₁'
    (fun z hz => exhaust l₁ hg z hz) _ _ (β (c₀ 1)) hJ₀ hJ hk₀
  rw [this, ← RingHom.comp_apply i₁ β, h1, hc1]

end GlobalTheory.MBLow.KeyTop
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyRuleConstantAlongDeformationOfClausesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.transfer_of_rule4' : ∀ κ : Rule, Rule4 κ → Transfer κ := by
  first | exact @GlobalTheory.MBLow.KeyTop.transfer_of_rule4 | exact GlobalTheory.MBLow.KeyTop.transfer_of_rule4 | (intros; apply GlobalTheory.MBLow.KeyTop.transfer_of_rule4 <;> assumption)
end
end
