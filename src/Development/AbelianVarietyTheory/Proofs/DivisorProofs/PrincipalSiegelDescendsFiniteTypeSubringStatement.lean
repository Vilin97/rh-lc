module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Data
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfGenerization
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.SiegelFamilyZetaUnit
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtale
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrincipalOfSubring
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfUnimodular
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleIsoLinCombSymmBiadditiveSubstitution
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeomPtSpecializes

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

noncomputable section

namespace GlobalTheory.LevelDescent

open GlobalTheory.SiegelPull GlobalTheory.CharZeroPts

theorem exists_geomPt_specializes (R : Type) [CommRing R] (R₁ : Subring R) (p : Sp R₁) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (z : Sp K ⟶ Sp R), ∀ u, (z ≫ spMap R₁.subtype) u ⤳ p := by
  haveI := p.isPrime
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R₁)) (J := p.asIdeal) bot_le
  obtain ⟨P, hP, hPq⟩ :=
    Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective (f := R₁.subtype) Subtype.val_injective q hq
  obtain ⟨K, _, _, t, ht⟩ := GlobalTheory.SiegelTypings.exists_geomPt (S := Sp R) ⟨P, hP⟩
  refine ⟨K, inferInstance, inferInstance, t, fun u => ?_⟩
  have e : t u = ⟨P, hP⟩ := by
    obtain ⟨v, hv⟩ := ht
    rw [Subsingleton.elim u v, hv]
  rw [Scheme.Hom.comp_apply, e]
  refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
  show P.comap R₁.subtype ≤ p.asIdeal
  rw [hPq]
  exact hqp

section Labels

variable {h M : ℕ}

def toStd : (Fin (h + h) → ZMod M) →+ IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.Std h M where
  toFun c := (fun i => c (Fin.castAdd h i), fun i => c (Fin.natAdd h i))
  map_zero' := rfl
  map_add' _ _ := rfl

theorem toStd_append (a : IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.Std h M) : toStd (Fin.append a.1 a.2) = a :=
  Prod.ext (funext fun i => Fin.append_left a.1 a.2 i) (funext fun i => Fin.append_right a.1 a.2 i)

theorem append_toStd (c : Fin (h + h) → ZMod M) : Fin.append (toStd c).1 (toStd c).2 = c :=
  Fin.append_castAdd_natAdd

theorem toStd_injective : Function.Injective (toStd (h := h) (M := M)) := fun c c' e => by
  rw [← append_toStd c, ← append_toStd c', e]

theorem sum_val_smul [NeZero M] (c : Fin (h + h) → ZMod M) :
    ∑ i, (c i).val • toStd (Pi.single i (1 : ZMod M)) = toStd c := by

  simp_rw [← map_nsmul, ← map_sum]
  congr 1
  conv_rhs => rw [← Finset.univ_sum_single c]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Pi.single_smul, nsmul_eq_mul, _root_.mul_one, ZMod.natCast_zmod_val]

end Labels

section Sections

variable {S : Scheme.{0}} {h M : ℕ} {A : Over S} [GrpObj A] {lv : IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.Std h M → (𝟙_ (Over S) ⟶ A)}

theorem lv_zero (add : ∀ a b, lv (a + b) = lv a * lv b) : lv 0 = 1 := by
  have e := add 0 0
  rw [add_zero] at e
  exact left_eq_mul.1 e

theorem lv_nsmul (add : ∀ a b, lv (a + b) = lv a * lv b) (n : ℕ) (a) : lv (n • a) = lv a ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, lv_zero add]
  | succ n ih => rw [succ_nsmul, add, ih, pow_succ]

theorem lv_pow (add : ∀ a b, lv (a + b) = lv a * lv b) (a) : lv a ^ M = 1 := by
  rw [← lv_nsmul add, show M • a = 0 by ext i <;> simp, lv_zero add]

theorem linComb_lv (add : ∀ a b, lv (a + b) = lv a * lv b) {T : Over S} (g : T ⟶ 𝟙_ (Over S)) :
    ∀ {r : ℕ} (v : Fin r → IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.Std h M) (n : Fin r → ℕ),
      Out.linComb (fun i => g ≫ lv (v i)) n = g ≫ lv (∑ i, n i • v i) := by
  intro r
  induction r with
  | zero =>
    intro v n
    simp [Out.linComb, lv_zero add]
  | succ r ih =>
    intro v n
    have e := ih (fun i => v i.succ) (fun i => n i.succ)
    simp only [Out.linComb] at e ⊢
    rw [List.ofFn_succ, List.prod_cons, e, Fin.sum_univ_succ, add, MonObj.comp_mul, lv_nsmul add,
      MonObj.comp_pow]

end Sections

end GlobalTheory.LevelDescent

namespace GlobalTheory.LevelDescent

open GlobalTheory.SiegelPull GlobalTheory.CharZeroPts

section Cond

variable {S : Scheme.{0}} {h M : ℕ} {A : Over S} [GrpObj A] {lv : IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.Std h M → (𝟙_ (Over S) ⟶ A)}

theorem cond_iff [NeZero M] (add : ∀ a b, lv (a + b) = lv a * lv b) {k : Type} [Field k] (x : Sp k ⟶ S) :
    ((Function.Injective fun a => toUnit (Over.mk x) ≫ lv a) ∧
      ∀ g : Over.mk x ⟶ A, g ^ M = 1 ↔ ∃ a, toUnit (Over.mk x) ≫ lv a = g) ↔
    ∀ y : Over.mk x ⟶ A, y ^ M = 1 → ∃! c : Fin (h + h) → ZMod M,
      Out.linComb (fun i => toB x ≫ lv (toStd (Pi.single i 1))) (fun i => (c i).val) = y := by
  have E : ∀ c : Fin (h + h) → ZMod M,
      Out.linComb (fun i => toB x ≫ lv (toStd (Pi.single i 1))) (fun i => (c i).val) =
        toUnit (Over.mk x) ≫ lv (toStd c) := fun c =>
    (linComb_lv add (toB x) _ _).trans (by rw [sum_val_smul]; rfl)
  have tors : ∀ a, (toUnit (Over.mk x) ≫ lv a) ^ M = 1 := fun a => by
    rw [← MonObj.comp_pow, lv_pow add, MonObj.comp_one]
  constructor
  · rintro ⟨inj, sp⟩ y hy
    obtain ⟨a, rfl⟩ := (sp y).1 hy
    refine ⟨Fin.append a.1 a.2, by beta_reduce; rw [E, toStd_append], fun c hc => toStd_injective ?_⟩
    rw [toStd_append]
    exact inj ((E c).symm.trans hc)
  · intro H
    refine ⟨fun a b e => ?_, fun g => ⟨fun hg => ?_, ?_⟩⟩
    · obtain ⟨c, -, hc⟩ := H _ (tors a)
      have ea := hc (Fin.append a.1 a.2) (by beta_reduce; rw [E, toStd_append])
      have eb := hc (Fin.append b.1 b.2) (by beta_reduce; rw [E, toStd_append]; exact e.symm)
      rw [← toStd_append a, ← toStd_append b, ea, eb]
    · obtain ⟨c, hc, -⟩ := H g hg
      exact ⟨toStd c, (E c).symm.trans hc⟩
    · rintro ⟨a, rfl⟩
      exact tors a

end Cond

section Transfer

variable {h M : ℕ} {S S₁ : Scheme.{0}} {A : Over S} [GrpObj A] {A₁ : Over S₁} [GrpObj A₁] {f : S ⟶ S₁}
  {φ : A.left ⟶ A₁.left} {lv : IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.Std h M → (𝟙_ (Over S) ⟶ A)}
  {lv₁ : IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.Std h M → (𝟙_ (Over S₁) ⟶ A₁)}

theorem push_lv (hp : IsGrpPullback A A₁ f φ) (hl : ∀ a, (lv a).left ≫ φ = f ≫ (lv₁ a).left) (T : Over S) (a) :
    pushHom hp T (toUnit T ≫ lv a) = toUnit (Over.mk (T.hom ≫ f)) ≫ lv₁ a := by
  apply Over.OverMorphism.ext
  show ((toUnit T).left ≫ (lv a).left) ≫ φ = (toUnit (Over.mk (T.hom ≫ f))).left ≫ (lv₁ a).left
  rw [Category.assoc, hl, Over.toUnit_left, Over.toUnit_left, ← Category.assoc]
  rfl

theorem cond_push (hp : IsGrpPullback A A₁ f φ) (hl : ∀ a, (lv a).left ≫ φ = f ≫ (lv₁ a).left) {k : Type} [Field k]
    (x : Sp k ⟶ S)
    (H : (Function.Injective fun a => toUnit (Over.mk x) ≫ lv a) ∧
      ∀ g : Over.mk x ⟶ A, g ^ M = 1 ↔ ∃ a, toUnit (Over.mk x) ≫ lv a = g) :
    (Function.Injective fun a => toUnit (Over.mk (x ≫ f)) ≫ lv₁ a) ∧
      ∀ g : Over.mk (x ≫ f) ⟶ A₁, g ^ M = 1 ↔ ∃ a, toUnit (Over.mk (x ≫ f)) ≫ lv₁ a = g := by
  have P := push_lv hp hl (Over.mk x)
  have inj := push_injective hp (Over.mk x)
  refine ⟨fun a b e => H.1 (inj ?_), fun g => ?_⟩
  · rw [P, P]
    exact e
  · obtain ⟨g', rfl⟩ := push_surjective hp (Over.mk x) g
    rw [← map_pow, ← map_one (pushHom hp (Over.mk x)), inj.eq_iff, H.2 g']
    refine exists_congr fun a => ?_
    rw [← inj.eq_iff, P]
    rfl

end Transfer

end GlobalTheory.LevelDescent

namespace GlobalTheory.LevelDescent

open GlobalTheory.SiegelPull GlobalTheory.CharZeroPts

theorem isLevel_of_subring : ∀ (h M : ℕ) (R : Type) [CommRing R] (R₁ : Subring R) (A : Over (Sp R)) [GrpObj A] (A₁ : Over (Sp R₁)) [GrpObj A₁] (φ : A.left ⟶ A₁.left) (lv : Std h M → (𝟙_ (Over (Sp R)) ⟶ A)) (lv₁ : Std h M → (𝟙_ (Over (Sp R₁)) ⟶ A₁)), 0 < M → IsUnit (M : R₁) → IsAbelianScheme A₁ → IsGrpPullback A A₁ (spMap R₁.subtype) φ → (∀ a, (lv a).left ≫ φ = spMap R₁.subtype ≫ (lv₁ a).left) → (∀ a b, lv₁ (a + b) = lv₁ a * lv₁ b) → IsLevel A lv → IsLevel A₁ lv₁ := by
  intro h M R _ R₁ A _ A₁ _ φ lv lv₁ hM hu hA hp hl hadd hlev
  haveI : NeZero M := ⟨hM.ne'⟩
  have hu' : IsUnit ((M : ℕ) : Γ(Sp R₁, ⊤)) := by
    simpa using hu.map (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom
  refine ⟨hadd, fun k _ _ x => (cond_iff hadd x).2 fun y hy => ?_⟩
  refine torsion_basis_of_generization A₁ M (h + h) (fun i => lv₁ (toStd (Pi.single i 1))) hA hM hu'
    (fun i => lv_pow hadd _) (fun p => ?_) k x y hy
  obtain ⟨K, _, _, z, hz⟩ := exists_geomPt_specializes R R₁ p
  exact ⟨K, inferInstance, inferInstance, z ≫ spMap R₁.subtype, hz,
    (cond_iff hadd _).1 (cond_push hp hl z (hlev.2 K z))⟩

end GlobalTheory.LevelDescent
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymplecticOfSubring

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

open GlobalTheory.EighthPower GlobalTheory.CechPic GlobalTheory.MatrixBundle GlobalTheory.ZM

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SympDescent

theorem translFixed_of_pair {S : Scheme.{0}} {h M : ℕ} (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left)
    (H : IsSymmetricPair h A P) (ha : Out.RelAmple A (diagPull A P)) (x : 𝟙_ (Over S) ⟶ A) (hx : x ^ M = 1) :
    (M : ℤ) • cls (diagPull A P) (pull_isLB H.2.2.1 _) =
      (M : ℤ) • pull ((toUnit A ≫ x) * 𝟙 A).left (cls (diagPull A P) (pull_isLB H.2.2.1 _)) := by
  haveI := H.1.comm
  have hP := H.2.2.1
  have hb : IsSymBilin (cls P hP) := isSymBilin_of_gen hP (fun T x x' y =>
    (Biadditive.biadditive_of_triv_axes globalFns_holds S A (diagPull A P) H.1 (pull_isLB hP _) ha P hP
      H.2.2.2.1 H.2.2.2.2.1 T x x' y).1) H.2.2.2.2.2
  have d : ∀ f : A ⟶ A, pull f.left (cls (diagPull A P) (pull_isLB hP _)) = pairCls (cls P hP) f f := fun f =>
    (pull_pairCls (cls P hP) f (𝟙 _) (𝟙 _)).trans (by rw [Category.comp_id])
  have z : ∀ y : A ⟶ A, (M : ℤ) • pairCls (cls P hP) (toUnit A ≫ x) y = 0 := fun y => by
    have e := BilinCalc.map_prod_zpow (fun z => pairCls (cls P hP) z y) (fun a b => hb.mul _ a b y)
      (fun _ : Fin 1 => toUnit A ≫ x) fun _ => (M : ℤ)
    simp only [Finset.univ_unique, Finset.prod_const, Finset.card_singleton, pow_one, Finset.sum_const, one_smul,
      zpow_natCast] at e
    rw [← e, ← MonObj.comp_pow, hx, MonObj.comp_one]
    exact one_left (hb.mul _) y
  rw [d, hb.mul, hb.symm _ (𝟙 A) (_ * _), hb.mul, smul_add, smul_add, z, z, zero_add, zero_add]
  rfl

theorem units_map_comp_appTop {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (u : Γ(Z, ⊤)ˣ) :
    Units.map (f ≫ g).appTop.hom.toMonoidHom u =
      Units.map f.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom u) :=
  Units.ext (by simp [Scheme.Hom.comp_appTop]; rfl)

theorem isSymplectic_of_subring : ∀ (h M : ℕ) (B R : Type) [CommRing B] [CommRing R] (ζ : Bˣ) (R₁ : Subring R) (s₁ : Sp R₁ ⟶ Sp B) (A : Over (Sp R)) [GrpObj A] (P : LB (A ⊗ A).left) (lv : Std h M → (𝟙_ (Over (Sp R)) ⟶ A)) (A₁ : Over (Sp R₁)) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (lv₁ : Std h M → (𝟙_ (Over (Sp R₁)) ⟶ A₁)), 0 < M → ζ ^ M = 1 → IsUnit (M : R₁) → IsSymmetricPair h A₁ P₁ → IsPrincipal A₁ P₁ → IsLevel A₁ lv₁ → P.IsLB → IsPullbackTriple A P lv A₁ P₁ lv₁ (spMap R₁.subtype) → IsSymplectic ζ (spMap R₁.subtype ≫ s₁) A P lv → IsSymplectic ζ s₁ A₁ P₁ lv₁ := by
  intro h M B R _ _ ζ R₁ s₁ A _ P lv A₁ _ P₁ lv₁ hM hζ hu H₁ H₂ H₃ hPR Hpb Hs
  haveI := H₁.1.comm
  have hP := H₁.2.2.1
  have hD : (diagPull A₁ P₁).IsLB := pull_isLB hP _
  have z₀ : lv₁ 0 = 1 := by
    have e := H₃.1 0 0
    rw [add_zero] at e
    exact left_eq_mul.1 e
  have tors : ∀ a, lv₁ a ^ M = 1 := fun a => by
    have e : ∀ n : ℕ, lv₁ (n • a) = lv₁ a ^ n := fun n => by
      induction n with
      | zero => rw [zero_smul, pow_zero, z₀]
      | succ n ih => rw [succ_nsmul, H₃.1, ih, pow_succ]
    rw [← e, show M • a = 0 by ext i <;> simp, z₀]
  have th : ∀ a (p : (𝟙_ (Over (Sp R₁))).left), ∃ V : (𝟙_ (Over (Sp R₁))).left.Opens, p ∈ V ∧
      ∃ θ : Out.ThetaGrp A₁ (diagPull A₁ P₁) M (Out.overRes V), θ.pt = Out.overResι V ≫ lv₁ a := fun a p => by
    let T := Out.overRes (T := 𝟙_ (Over (Sp R₁))) ⊤
    have hT : (Out.thetaLB A₁ (diagPull A₁ P₁) M (Out.overResι ⊤ ≫ lv₁ a)).IsLB := LB.isLB_linComb hD _ _
    obtain ⟨t, ht⟩ := (cls_eq_zero_iff hT).1 (by
      unfold Out.thetaLB at hT ⊢
      rw [cls_linComb hD, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, neg_smul]
      have e : Out.translPt A₁ (Out.overResι ⊤ ≫ lv₁ a) = snd T A₁ ≫ ((toUnit A₁ ≫ lv₁ a) * 𝟙 A₁) := by
        rw [MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc, Out.translPt, ← Hom.mul_def, ← Category.assoc,
          toUnit_unique (fst _ _ ≫ _) (toUnit _)]
      rw [e, Over.comp_left, pull_comp, ← map_zsmul, ← map_zsmul,
        ← GlobalTheory.SympDescent.translFixed_of_pair A₁ P₁ H₁ H₂.1 (lv₁ a) (tors a), add_neg_cancel])
    exact ⟨⊤, trivial, ⟨_, t, ht⟩, rfl⟩
  obtain ⟨φ, φ₂, pb, s₁', s₂', iso, hl⟩ := Hpb
  have hdi : LBIso (diagPull A P) ((diagPull A₁ P₁).pull φ) := GlobalTheory.SiegelPull.diag_iso ⟨s₁', s₂'⟩ iso
  have hL : (diagPull A P).IsLB := pull_isLB hPR _

  have inj : Function.Injective ((𝟙_ (Over (Sp R))).hom ≫ spMap R₁.subtype).appTop.hom := by
    have u₁ : (𝟙_ (Over (Sp R))).hom = 𝟙 _ := rfl
    rw [u₁, Category.id_comp]
    have k : ∀ z, (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((spMap R₁.subtype).appTop.hom z) =
        ((Scheme.ΓSpecIso (CommRingCat.of R₁)).hom.hom z : R) := fun z => by
      have e := congrArg (fun q => q.hom z) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom R₁.subtype))
      first
        | exact e
        | (simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, Subring.subtype_apply] at e; exact e)
    intro x y hxy
    have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom hxy
    rw [k, k] at h2
    have h3 := congrArg (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (Subtype.val_injective h2)
    simpa using h3
  intro a b
  obtain ⟨c, hc⟩ := CommutatorPairing.exists_weilIs globalFns_holds H₁.1 hD (th a) (th b)
  let X' : Over (Sp R₁) := Over.mk ((𝟙_ (Over (Sp R))).hom ≫ spMap R₁.subtype)
  have ex : ∀ a, (toUnit X' ≫ lv₁ a).left = (lv a).left ≫ φ := fun a => by
    rw [Over.comp_left, Over.toUnit_left, hl a]
    exact Category.assoc _ _ _
  have w := (weilIs_grpPullback_of_comm (Sp R₁) (Sp R) A₁ A (spMap R₁.subtype) φ (diagPull A₁ P₁) (diagPull A P)
    hD hL pb hdi (𝟙_ (Over (Sp R))) M (lv a) (lv b) (toUnit X' ≫ lv₁ a) (toUnit X' ≫ lv₁ b) _ (ex a) (ex b)).1 (Hs a b)
  have w' := CommPairing.weilIs_pull globalFns_holds H₁.1 hD (toUnit X') hc
  have q := CommutatorPairing.weilIs_unique globalFns_holds H₁.1 hD w' w
  have u₂ : (𝟙_ (Over (Sp R₁))).hom = 𝟙 _ := rfl
  have hinj : Function.Injective (Units.map (toUnit X').left.appTop.hom.toMonoidHom) := fun u v huv =>
    Units.ext (inj (by
      have := congrArg Units.val huv
      simp only [Units.coe_map, MonoidHom.coe_coe, Over.toUnit_left] at this
      exact this))
  have q₂ : Units.map (toUnit X').left.appTop.hom.toMonoidHom
      (Units.map ((𝟙_ (Over (Sp R₁))).hom ≫ s₁).appTop.hom.toMonoidHom (unitOn (ζ ^ (2 * stdForm a b).val))) =
      Units.map ((𝟙_ (Over (Sp R))).hom ≫ spMap R₁.subtype ≫ s₁).appTop.hom.toMonoidHom
        (unitOn (ζ ^ (2 * stdForm a b).val)) := by
    rw [← GlobalTheory.SympDescent.units_map_comp_appTop, Over.toUnit_left, u₂, Category.id_comp]
    rfl
  rw [← hinj (q.trans q₂.symm)]
  exact hc

end GlobalTheory.SympDescent
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelDescendsFiniteTypeSubring

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

namespace GlobalTheory.SiegFG

theorem siegPre_descends_fg : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (R : Type) [CommRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ (R₀ : Subring R) (β₀ : cycAway n →+* R₀) (c₀ : SiegPre g n (zetaAway n) (spMap β₀)), Algebra.FiniteType ℤ R₀ ∧ R₀.subtype.comp β₀ = β ∧ c₀.Principal ∧ SiegPB c c₀ (spMap R₀.subtype) := by
  intro g n hn hodd R _ β c hc
  have hn0 : n ≠ 0 := by omega
  obtain ⟨R₀, β₀, A₀, _, P₀, lv₀, hft, hβ, hsym, hadd, hamp, hpb⟩ := GlobalTheory.SiegFGData.data g n hn hodd R β c hc
  have : IsNoetherianRing R₀ := Algebra.FiniteType.isNoetherianRing ℤ R₀
  have hpb' := hpb
  obtain ⟨φ, φ₂, hφ, s₁, s₂, iso, hl⟩ := hpb
  have hpr : IsPrincipal A₀ P₀ :=
    GlobalTheory.PrincSubring.isPrincipal_of_subring g R R₀ c.A c.P A₀ P₀ φ φ₂ hsym hamp hφ ⟨s₁, s₂⟩ iso ((principal_iff c).1 hc)
  let u : (cycAway n)ˣ := Units.ofPowEqOne (zetaAway n) n (zetaAway_pow_self hn0) hn0
  have hζ : u ^ n = 1 := Units.ext (by simp [u])
  have hunit : IsUnit (n : R₀) := by simpa using (isUnit_natCast hn0).map β₀
  have hlevR : IsLevel c.A (lvOf c) := isLevel_lvOf (ζ := u) c
  have hlev₀ : IsLevel A₀ lv₀ :=
    GlobalTheory.LevelDescent.isLevel_of_subring g n R R₀ c.A A₀ φ (lvOf c) lv₀ (by omega) hunit hsym.1 hφ hl hadd hlevR
  have hsympR : IsSymplectic u (spMap β) c.A c.P (lvOf c) :=
    isSymplectic_of_translFixed (ζ := u) hn0 hζ (isUnit_natCast hn0) c (translFixed_of_ample c hc.1)
  have hsymp₀ : IsSymplectic u (spMap β₀) A₀ P₀ lv₀ :=
    GlobalTheory.SympDescent.isSymplectic_of_subring g n (cycAway n) R u R₀ (spMap β₀) c.A c.P (lvOf c) A₀ P₀ lv₀ (by omega) hζ hunit hsym hpr hlev₀
      c.isLB hpb' (by rw [← GlobalTheory.SiegelTypings.spMap_comp, hβ]; exact hsympR)
  let c₀ : SiegPre g n (zetaAway n) (spMap β₀) := ofTriple (ζ := u) hn0 hζ A₀ P₀ lv₀ hsym hlev₀ hsymp₀
  refine ⟨R₀, β₀, c₀, hft, hβ, ?_, (siegPB_iff c c₀ _).2 ?_⟩
  · apply (principal_iff c₀).2
    change IsPrincipal A₀ P₀
    exact hpr
  · change IsPullbackTriple c.A c.P (lvOf c) A₀ P₀ (lvOf (ofTriple (ζ := u) hn0 hζ A₀ P₀ lv₀ hsym hlev₀ hsymp₀)) (spMap R₀.subtype)
    rw [lvOf_ofTriple]
    exact hpb'

end GlobalTheory.SiegFG
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelDescendsFiniteTypeSubringStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.principalSiegel_descends_finiteType_subring : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (R : Type) [CommRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ (R₀ : Subring R) (β₀ : cycAway n →+* R₀) (c₀ : SiegPre g n (zetaAway n) (spMap β₀)), Algebra.FiniteType ℤ R₀ ∧ R₀.subtype.comp β₀ = β ∧ c₀.Principal ∧ SiegPB c c₀ (spMap R₀.subtype) := by
  first | (exact @GlobalTheory.SiegFG.siegPre_descends_fg) | (exact GlobalTheory.SiegFG.siegPre_descends_fg) | (intros; apply GlobalTheory.SiegFG.siegPre_descends_fg  <;> assumption)
end
end
