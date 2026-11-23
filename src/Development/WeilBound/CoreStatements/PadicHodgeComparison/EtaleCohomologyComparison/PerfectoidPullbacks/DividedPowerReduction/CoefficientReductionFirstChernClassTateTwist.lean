module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.IsFirstChernThickening
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.JEqPdPow
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClsEqOfEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientReductionFirstChernClassTateTwist
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueIsFirstChernTorsionFree
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstChernPullback
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullRetype
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullUnitClass
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedKillsToSome
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedTrans

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsFirstChernThickeningMuBOfIsFirstChernDeRham

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.FirstChernRationalLift

variable {K B' : Type} [Field K] [CharZero K] [CommRing B'] [Algebra K B'] {I : Ideal B'} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of K)) (s : ℕ)

abbrev famK {C : Type 1} [Category.{0} C] (G : C ⥤ (TS γ q 1 s {⊤}).FullSubcategory) : C ⥤ Thick (smFun X q) :=
  G ⋙ (smO γ q 1 s {⊤}).G ⋙ (TO q 1 s {⊤}).ι

theorem pt_famK {C : Type 1} [Category.{0} C] (G : C ⥤ (TS γ q 1 s {⊤}).FullSubcategory) (c : C) :
    pt ((famK γ q s G).obj c) = pt (G.obj c).obj := Category.comp_id _

def liftK {C : Type 1} [Category.{0} C] {G : C ⥤ (TS γ q 1 s {⊤}).FullSubcategory} {D : E.LineData X}
    (Λ : B.CLift (q := q) (b := nlBase B' I γ 0) (ht := rfl) (κ := κA K I) (G ⋙ (TS γ q 1 s {⊤}).ι) D) :
    CLiftK (famK γ q s G) D where
  p c := Λ.p c
  hp c := (Λ.hp c).trans (Category.comp_id _).symm
  w φ := Λ.w φ
  hw φ h := Λ.hw φ h

theorem isFirstChernThickening_muB_of_isFirstChernDeRham (D : E.LineData X) (c : HdR q 2)
    (h : IsFirstChernDeRham (q := q) D c) :
    IsFirstChernThickening (TS γ q 1 s {⊤}) D s (muB γ q 1 s {⊤} 2 c) := by
  intro C _ G hG Λ
  have hpd : ∀ c', ((famK γ q s G).obj c').pdPow s = ⊥ := fun c' => ((smO γ q 1 s {⊤}).G.obj (G.obj c')).property.1.1
  have hV : ∀ c', ∃ (V : X.Opens) (σ : (V : Scheme.{0}) ⟶ D.Y), σ ≫ D.f = V.ι ∧ InU V ((famK γ q s G).obj c') := by
    intro c'
    obtain ⟨V, ⟨σ, hσ⟩, hU⟩ := hG c'
    refine ⟨V, σ, hσ, ?_⟩
    unfold InU
    rw [pt_famK]
    exact hU
  obtain ⟨z, hz, hzv, hcls⟩ := h s C (famK γ q s G) hpd hV (liftK γ q s Λ)
  let m' : CH.Mor (famK γ q s G ⋙ O (smFun X q)) (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) (algebraMap K B') :=
    ⟨𝟭 _, fun T => (smO γ q 1 s {⊤}).o.τ (G.obj T), fun φ x => (smO γ q 1 s {⊤}).o.nat (G.map φ) x⟩
  have e : (show CH.Cn (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2 from Λ.coc (RingHom.id _) s) = m'.pullC 2 z := by
    funext σ
    exact (hzv σ).symm
  have hb : CH.d (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2 (m'.pullC 2 z) = 0 := by
    rw [m'.d_pullC, hz, map_zero]
  have hz' : CH.d (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2 (Λ.coc (RingHom.id _) s) = 0 := (congrArg (CH.d (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2) e).trans hb
  refine ⟨hz', ?_⟩
  have e1 := CrystallineSemistableComparison.P.mapH_cls m'.hom 2 z hz hb
  have e2 : (CH.Mor.restrict (CH.modF (sP (TS γ q 1 s {⊤})).A) G).pull 2 (muB γ q 1 s {⊤} 2 c) =
      m'.pull 2 ((CH.Mor.restrict (O (smFun X q)) (famK γ q s G)).pull 2 c) := by
    have a1 := (CrystallineSemistableComparison.P.pull_comp (CH.Mor.restrict (O (smFun X q)) (TO q 1 s {⊤}).ι) (smO γ q 1 s {⊤}).o 2 c).1
    have a2 := (CrystallineSemistableComparison.P.pull_comp ((CH.Mor.restrict (O (smFun X q)) (TO q 1 s {⊤}).ι).comp (smO γ q 1 s {⊤}).o)
      (CH.Mor.restrict (CH.modF (sP (TS γ q 1 s {⊤})).A) G) 2 c).1
    have b := (CrystallineSemistableComparison.P.pull_comp (CH.Mor.restrict (O (smFun X q)) (famK γ q s G)) m' 2 c).1
    exact (congrArg ((CH.Mor.restrict (CH.modF (sP (TS γ q 1 s {⊤})).A) G).pull 2) a1.symm).trans (a2.symm.trans b)
  rw [e2, ← hcls]
  refine Eq.trans ?_ e1.symm
  have key : ∀ (a : CH.Cn (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2) (ha : CH.d (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2 a = 0),
      a = m'.pullC 2 z → (CH.cx (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A)).cls a ha =
        (CH.cx (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A)).cls (m'.pullC 2 z) hb := by
    rintro _ _ rfl
    rfl
  exact key _ hz' e

end GlobalTheory.CompanionTheory.FirstChernRationalLift
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullSqLePullToSq

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.RedTower

section Sq
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

theorem pull_sqLe_pull_toSq {a b a' b' : IdF A} (ha : ∀ T, a.S T = ⊤) (ha' : ∀ T, a'.S T = ⊤)
    (hle : ∀ T, a.S T ≤ a'.S T) (hb : ∀ T, b.S T ≤ b'.S T) (j : ℕ) (z : CH.H (CH.modF A) j) :
    (sqLe hle hb).pull j ((toSq a b ha).pull j z) = (toSq a' b' ha').pull j z := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rfl

end Sq

theorem trM_redM {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)) (r : Option ℤ) (c : b.R) (n j : ℕ) (z : HO Q j) :
    trM Q r c n j (redM Q r (c ^ (n + 1)) j z) = redM Q r (c ^ n) j z :=
  pull_sqLe_pull_toSq (fun _ => rfl) (fun _ => rfl) (fun _ => le_rfl) (stdI_le Q r c n) j z

end GlobalTheory.CompanionTheory.RedTower
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedMCup

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.RedCup

theorem redM_cup {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)) (r : Option ℤ) (c : b.R) {i j k : ℕ} (h : i + j = k)
    (x : HO Q i) (y : HO Q j) :
    redM Q r c k ((CH.mulP (sP Q).A).cup h x y) = (sqP (stdI Q r c)).cup h (redM Q r c i x) (redM Q r c j y) := by
  have hm : ∀ T (u v : (CH.modF (sP Q).A).obj ((𝟭 _).obj T)),
      (toSq (IdF.top _) (stdI Q r c) fun _ => rfl).τ T ((CH.mulP (sP Q).A).μ _ u v) =
        (sqP (stdI Q r c)).μ T ((toSq (IdF.top _) (stdI Q r c) fun _ => rfl).τ T u)
          ((toSq (IdF.top _) (stdI Q r c) fun _ => rfl).τ T v) := fun _ _ _ => rfl
  exact CrystallineSemistableComparison.P.cup_pull (CH.mulP (sP Q).A) (sqP (stdI Q r c)) (𝟭 _)
    (toSq (IdF.top _) (stdI Q r c) fun _ => rfl).τ (toSq (IdF.top _) (stdI Q r c) fun _ => rfl).τ
    (toSq (IdF.top _) (stdI Q r c) fun _ => rfl).τ (toSq (IdF.top _) (stdI Q r c) fun _ => rfl).nat
    (toSq (IdF.top _) (stdI Q r c) fun _ => rfl).nat (toSq (IdF.top _) (stdI Q r c) fun _ => rfl).nat hm h x y

end GlobalTheory.CompanionTheory.RedCup
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedMorCupOne

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.RedCup

universe w w' w'' u v u' v' u'' v''

theorem one_cyc {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (A : C ⥤ CommAlgCat.{w} R) :
    (CH.cx (CH.modF A)).d 0 (fun s => (1 : A.obj (s.obj (Fin.last 0)))) = 0 := by
  funext s
  change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (A.map (GlobalTheory.CatH.toLast i s)).hom 1 = (0 : A.obj _)
  rw [Fin.sum_univ_two, map_one, map_one]
  simp

theorem pull_oneH_eq {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {C : Type u} [Category.{v} C]
    {C' : Type u'} [Category.{v'} C'] {C'' : Type u''} [Category.{v''} C'']
    {σ : R →+* R''} {σ' : R' →+* R''} (A : C ⥤ CommAlgCat.{w} R) (A' : C' ⥤ CommAlgCat.{w'} R')
    {E : C'' ⥤ ModuleCat.{w''} R''} (m : CH.Mor (CH.modF A) E σ) (m' : CH.Mor (CH.modF A') E σ')
    (h : ∀ T : C'', m.τ T (1 : A.obj (m.G.obj T)) = m'.τ T (1 : A'.obj (m'.G.obj T))) :
    m.pull 0 (CH.oneH A) = m'.pull 0 (CH.oneH A') := by
  have e : m.hom.f 0 (fun s : ComposableArrows C 0 => (1 : A.obj (s.obj (Fin.last 0)))) =
      m'.hom.f 0 (fun s : ComposableArrows C' 0 => (1 : A'.obj (s.obj (Fin.last 0)))) :=
    funext fun s => h (s.obj (Fin.last 0))
  have c : (CH.cx E).d 0 (m.hom.f 0 (fun s : ComposableArrows C 0 => (1 : A.obj (s.obj (Fin.last 0))))) = 0 := by
    rw [m.hom.comm, one_cyc, map_zero]
  have c' : (CH.cx E).d 0 (m'.hom.f 0 (fun s : ComposableArrows C' 0 => (1 : A'.obj (s.obj (Fin.last 0))))) = 0 := by
    rw [m'.hom.comm, one_cyc, map_zero]
  unfold CH.Mor.pull CH.oneH
  refine (CrystallineSemistableComparison.P.mapH_cls m.hom 0 _ _ c).trans (Eq.trans ?_ (CrystallineSemistableComparison.P.mapH_cls m'.hom 0 _ _ c').symm)
  exact congrArg Submodule.Quotient.mk (Subtype.ext e)

theorem redMor_mul {O A R Λ : Type} [CommRing O] [CommRing A] [CommRing R] [CommRing Λ] [Algebra O A] {I : Ideal A} {γ : DividedPowers I}
    {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ} (d : RedIn δ κ γ l n) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (s : ℕ) (𝒱 : Set X.Opens) (c : Λ →+* R) (lam : Λ →+* A)
    (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a)) (r : Option ℤ) (T)
    (x y : (B.OM (nlFun δ l X q κ) c).obj ((redMor q s d 𝒱 c lam hc r).G.obj T)) :
    (redMor q s d 𝒱 c lam hc r).τ T ((CH.mulP (B.OA (nlFun δ l X q κ) c)).μ _ x y) =
      (sqP (stdI (TS γ q l s 𝒱) r ((l : A) ^ n))).μ T ((redMor q s d 𝒱 c lam hc r).τ T x) ((redMor q s d 𝒱 c lam hc r).τ T y) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective (I := lnT T.obj l n) x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := lnT T.obj l n) y
  refine Subtype.ext ?_
  rfl

theorem redMor_cup_one {O A R Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R] [CommRing Λ] {I : Ideal A} {γ : DividedPowers I}
    {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ} (d : RedIn δ κ γ l n) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (s : ℕ) (𝒱 : Set X.Opens) (c : Λ →+* R) (lam : Λ →+* A)
    (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a)) (r : Option ℤ) :
    (∀ {i j k : ℕ} (h : i + j = k) x y, (redMor q s d 𝒱 c lam hc r).pull k ((CH.mulP (B.OA (nlFun δ l X q κ) c)).cup h x y) =
      (sqP (stdI (TS γ q l s 𝒱) r ((l : A) ^ n))).cup h ((redMor q s d 𝒱 c lam hc r).pull i x) ((redMor q s d 𝒱 c lam hc r).pull j y)) ∧
    (redMor q s d 𝒱 c lam hc r).pull 0 (CH.oneH (B.OA (nlFun δ l X q κ) c)) =
      redM (TS γ q l s 𝒱) r ((l : A) ^ n) 0 (CH.oneH (sP (TS γ q l s 𝒱)).A) := by
  refine ⟨fun {i j k} h x y => ?_, ?_⟩
  · exact CrystallineSemistableComparison.P.cup_pull (CH.mulP (B.OA (nlFun δ l X q κ) c)) (sqP (stdI (TS γ q l s 𝒱) r ((l : A) ^ n)))
      (redMor q s d 𝒱 c lam hc r).G (redMor q s d 𝒱 c lam hc r).τ (redMor q s d 𝒱 c lam hc r).τ
      (redMor q s d 𝒱 c lam hc r).τ (redMor q s d 𝒱 c lam hc r).nat (redMor q s d 𝒱 c lam hc r).nat
      (redMor q s d 𝒱 c lam hc r).nat (redMor_mul d q s 𝒱 c lam hc r) h x y
  · exact pull_oneH_eq _ _ (redMor q s d 𝒱 c lam hc r) (toSq (IdF.top _) (stdI (TS γ q l s 𝒱) r ((l : A) ^ n)) fun _ => rfl)
      fun T => Subtype.ext (by
        change Ideal.Quotient.factor (ln_le q s 𝒱 r T) 1 = 1
        exact map_one _)

end GlobalTheory.CompanionTheory.RedCup
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.CoefficientReductionFirstChernClassTateTwist

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

theorem red_nm : ∀ {O A₁ A₂ R₁ R₂ Λ₁ Λ₂ : Type} [CommRing O] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [CommRing R₁]
    [CommRing R₂] [CommRing Λ₁] [CommRing Λ₂] {I₁ : Ideal A₁} {I₂ : Ideal A₂} {γ₁ : DividedPowers I₁} {γ₂ : DividedPowers I₂}
    {J₁ : Ideal R₁} {J₂ : Ideal R₂} {δ₁ : DividedPowers J₁} {δ₂ : DividedPowers J₂} {κ₁ : O →+* R₁ ⧸ J₁} {κ₂ : O →+* R₂ ⧸ J₂}
    {l n : ℕ} (d₁ : RedIn δ₁ κ₁ γ₁ l n) (d₂ : RedIn δ₂ κ₂ γ₂ l n) {X₁ X₂ : Scheme.{0}} {q₁ : X₁ ⟶ Spec (CommRingCat.of O)}
    {q₂ : X₂ ⟶ Spec (CommRingCat.of O)} (s : ℕ) {σ : A₁ →+* A₂} (nm : NMor γ₁ q₁ (κA O I₁) γ₂ q₂ (κA O I₂) σ) {σ' : R₁ →+* R₂}
    (m : Mor (nlFun δ₁ l X₁ q₁ κ₁) (nlFun δ₂ l X₂ q₂ κ₂) σ') (c₁ : Λ₁ →+* R₁) (c₂ : Λ₂ →+* R₂) (lam₁ : Λ₁ →+* A₁) (lam₂ : Λ₂ →+* A₂)
    (hc₁ : ∀ a, d₁.ρ (c₁ a) = Ideal.Quotient.mk _ (lam₁ a)) (hc₂ : ∀ a, d₂.ρ (c₂ a) = Ideal.Quotient.mk _ (lam₂ a))
    (σ₀ : Λ₁ →+* Λ₂) (h₀ : ∀ a, σ' (c₁ a) = c₂ (σ₀ a)),
    (∀ (B : CommRingCat.{0}) (y : PtOver X₂ q₂ κ₂ B), (show PtOver X₁ q₁ κ₁ B from m.pt.app B y).1.2 = y.1.2 ≫ nm.u) →
    (∀ x, d₂.ρ (σ' x) = lnMap σ l le_rfl (d₁.ρ x)) → ∀ (r : Option ℤ) (j : ℕ) (x : CH.H (B.OM (nlFun δ₁ l X₁ q₁ κ₁) c₁) j),
    (redMor q₂ s d₂ {⊤} c₂ lam₂ hc₂ r).pull j ((B.omMor m σ₀ h₀).pull j x) =
      nmHM nm l s r n j ((redMor q₁ s d₁ {⊤} c₁ lam₁ hc₁ r).pull j x) := @GlobalTheory.CompanionTheory.RedNat.red_nm

theorem red_tr : ∀ {O A R₁ R₂ Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R₁] [CommRing R₂] [CommRing Λ]
    {I : Ideal A} {γ : DividedPowers I} {J₁ : Ideal R₁} {J₂ : Ideal R₂} {δ₁ : DividedPowers J₁} {δ₂ : DividedPowers J₂}
    {κ₁ : O →+* R₁ ⧸ J₁} {κ₂ : O →+* R₂ ⧸ J₂} {l n : ℕ} (d₁ : RedIn δ₁ κ₁ γ l (n + 1)) (d₂ : RedIn δ₂ κ₂ γ l n) {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} (s : ℕ) (𝒱 : Set X.Opens) {σ' : R₁ →+* R₂} (m : Mor (nlFun δ₁ l X q κ₁) (nlFun δ₂ l X q κ₂) σ')
    (c₁ : Λ →+* R₁) (c₂ : Λ →+* R₂) (lam : Λ →+* A) (hc₁ : ∀ a, d₁.ρ (c₁ a) = Ideal.Quotient.mk _ (lam a))
    (hc₂ : ∀ a, d₂.ρ (c₂ a) = Ideal.Quotient.mk _ (lam a)) (h₀ : ∀ a, σ' (c₁ a) = c₂ (RingHom.id Λ a)),
    (∀ (B : CommRingCat.{0}) (y : PtOver X q κ₂ B), (show PtOver X q κ₁ B from m.pt.app B y).1.2 = y.1.2) →
    (∀ x, d₂.ρ (σ' x) = lnMap (RingHom.id A) l n.le_succ (d₁.ρ x)) → ∀ (r : Option ℤ) (j : ℕ) (x : CH.H (B.OM (nlFun δ₁ l X q κ₁) c₁) j),
    (redMor q s d₂ 𝒱 c₂ lam hc₂ r).pull j ((B.omMor m (RingHom.id Λ) h₀).pull j x) =
      trM (TS γ q l s 𝒱) r (l : A) n j ((redMor q s d₁ 𝒱 c₁ lam hc₁ r).pull j x) := @GlobalTheory.CompanionTheory.RedTrans.red_trans

theorem red_cup : ∀ {O A R Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R] [CommRing Λ] {I : Ideal A} {γ : DividedPowers I}
    {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ} (d : RedIn δ κ γ l n) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (s : ℕ) (𝒱 : Set X.Opens) (c : Λ →+* R) (lam : Λ →+* A)
    (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a)) (r : Option ℤ),
    (∀ {i j k : ℕ} (h : i + j = k) x y, (redMor q s d 𝒱 c lam hc r).pull k ((CH.mulP (B.OA (nlFun δ l X q κ) c)).cup h x y) =
      (sqP (stdI (TS γ q l s 𝒱) r ((l : A) ^ n))).cup h ((redMor q s d 𝒱 c lam hc r).pull i x) ((redMor q s d 𝒱 c lam hc r).pull j y)) ∧
    (redMor q s d 𝒱 c lam hc r).pull 0 (CH.oneH (B.OA (nlFun δ l X q κ) c)) =
      redM (TS γ q l s 𝒱) r ((l : A) ^ n) 0 (CH.oneH (sP (TS γ q l s 𝒱)).A) := @GlobalTheory.CompanionTheory.RedCup.redMor_cup_one

theorem redM_cup : ∀ {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)) (r : Option ℤ) (c : b.R) {i j k : ℕ} (h : i + j = k)
    (x : HO Q i) (y : HO Q j), redM Q r c k ((CH.mulP (sP Q).A).cup h x y) = (sqP (stdI Q r c)).cup h (redM Q r c i x) (redM Q r c j y) := @GlobalTheory.CompanionTheory.RedCup.redM_cup

theorem smor_cup : ∀ {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {Φ : PDF R C}
    {Φ' : PDF R' C'} {σ : R →+* R'} (m : SMor Φ Φ' σ), (∀ {i j k : ℕ} (h : i + j = k) x y,
      m.o.pull k ((CH.mulP Φ.A).cup h x y) = (CH.mulP Φ'.A).cup h (m.o.pull i x) (m.o.pull j y)) ∧
    m.o.pull 0 (CH.oneH Φ.A) = CH.oneH Φ'.A := @GlobalTheory.CompanionTheory.SiteCup.smor_cup

theorem red_fil : ∀ {O A R Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R] [CommRing Λ] {I : Ideal A} {γ : DividedPowers I}
    {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ} (d : RedIn δ κ γ l n) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (s : ℕ) (𝒱 : Set X.Opens) (c : Λ →+* R) (lam : Λ →+* A)
    (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a)) (r j : ℕ), ∀ x ∈ (B.pdS (nlFun δ l X q κ) c r).img j,
    toSome (TS γ q l s 𝒱) r ((l : A) ^ n) j ((redMor q s d 𝒱 c lam hc none).pull j x) = 0 := @GlobalTheory.CompanionTheory.RedFil.red_kills_toSome

theorem thickening_firstChern_existsUnique : ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (l s : ℕ) (D : E.LineData X), sSup (𝒱D D) = ⊤ → ∃! z, IsFirstChernThickening (TS γ q l s {⊤}) D s z := @GlobalTheory.CompanionTheory.CrystallineFirstChernTorsionFree.existsUnique_isFirstChernTorsionFree

theorem coefficientReduction_firstChernClass_tateTwist : ∀ {O A R Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R] [CommRing Λ] {I : Ideal A} {γ : DividedPowers I}
    {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ} (d : RedIn δ κ γ l n) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (s : ℕ) (c : Λ →+* R) (lam : Λ →+* A) (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a))
    (D : E.LineData X), sSup (𝒱D D) = ⊤ → ∀ (x : CH.H (B.OM (nlFun δ l X q κ) c) 2) (z : HO (TS γ q l s {⊤}) 2),
    B.IsFirstChernClassOfLineBundle (q := q) (b := nlBase R J δ l) (ht := rfl) (κ := κ) D c (l * n) x → IsFirstChernThickening (TS γ q l s {⊤}) D s z →
    redM (TS γ q l s {⊤}) none ((l : A) ^ n) 2 z = (redMor q s d {⊤} c lam hc none).pull 2 x := @GlobalTheory.CompanionTheory.ReductionFirstChern.coefficientReduction_firstChernClass_tateTwist

theorem thickening_firstChern_pullback : ∀ {O O' R R' : Type} [CommRing O] [CommRing O'] [CommRing R] [CommRing R'] {I : Ideal R} {I' : Ideal R'}
    {γ : DividedPowers I} {γ' : DividedPowers I'} {X X' : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {q' : X' ⟶ Spec (CommRingCat.of O')}
    {κ : O →+* R ⧸ I} {κ' : O' →+* R' ⧸ I'} {σ : R →+* R'} (m : NMor γ q κ γ' q' κ' σ) {p : ℕ}
    (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (Q₀ : ObjectProperty (Thick (nlFun γ' p X' q' κ'))) (hQ : Used Q₀)
    (h : ∀ T, St Q₀ {⊤} T → Q ((m.mor p).obj T)) (D : E.LineData X) (N : ℕ) (z : HO Q 2) (z' : HO (St Q₀ {⊤}) 2),
    sSup (𝒱D D) = ⊤ → IsFirstChernThickening Q D N z → IsFirstChernThickening (St Q₀ {⊤}) (D.pb m.u) N z' → (m.smor Q (St Q₀ {⊤}) h).o.pull 2 z = z' := @GlobalTheory.CompanionTheory.FirstChernPullback.firstChern_pullback

theorem deRham_firstChern_to_thickening : ∀ {K B' : Type} [Field K] [CharZero K] [CommRing B'] [Algebra K B'] {I : Ideal B'} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of K)) (s : ℕ) (D : E.LineData X) (c : HdR q 2), IsFirstChernDeRham q D c →
    IsFirstChernThickening (TS γ q 1 s {⊤}) D s (muB γ q 1 s {⊤} 2 c) := @GlobalTheory.CompanionTheory.FirstChernRationalLift.isFirstChernThickening_muB_of_isFirstChernDeRham

theorem trM_redM : ∀ {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)) (r : Option ℤ) (c : b.R) (n j : ℕ) (z : HO Q j),
    trM Q r c n j (redM Q r (c ^ (n + 1)) j z) = redM Q r (c ^ n) j z := @GlobalTheory.CompanionTheory.RedTower.trM_redM

theorem nmHM_redM : ∀ {O A A' : Type} [CommRing O] [CommRing A] [CommRing A'] [Algebra O A] [Algebra O A'] {I : Ideal A} {I' : Ideal A'}
    {γ : DividedPowers I} {γ' : DividedPowers I'} {X X' : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {q' : X' ⟶ Spec (CommRingCat.of O)}
    {σ : A →+* A'} (m : NMor γ q (κA O I) γ' q' (κA O I') σ) (l s : ℕ) (r : Option ℤ) (n j : ℕ) (z : HO (TS γ q l s {⊤}) j),
    nmHM m l s r n j (redM (TS γ q l s {⊤}) r ((l : A) ^ n) j z) = redM (TS γ' q' l s {⊤}) r ((l : A') ^ n) j (nmHO m l s j z) := @GlobalTheory.CompanionTheory.RedPull.nmHM_redM

end CrystallineSemistableComparison.Pb
end
end
end
