module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeFinrankLa
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectOverLieTateLocusStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepAdjointActionLevelSiegelPullbackStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiFor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackBis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedLineBundlesCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieTateLociClosedSiegelPullbackStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectMapOfCommonPullback

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.HTObjMap

theorem exists_objMap_of_common_pullback : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S₀ : Scheme.{0}) (A₀ : Over S₀) [GrpObj A₀] (P₀ : LB (G2 A₀).left), P₀.IsLB → ∀ (T Z : Scheme.{0}) (t₁ : T ⟶ Sp R) (t₂ : Z ⟶ Sp R) (o : Obj b N t₁) (u : Obj b N t₂) (g : T ⟶ S₀) (πZ : Z ⟶ S₀) (z : T ⟶ Z) (φo : o.A.left ⟶ A₀.left) (φ₂o : (G2 o.A).left ⟶ (G2 A₀).left) (φu : u.A.left ⟶ A₀.left) (φ₂u : (G2 u.A).left ⟶ (G2 A₀).left) (ψ : o.A.left ⟶ u.A.left), IsGrpPullback o.A A₀ g φo → IsSquare φo φ₂o → LBIso o.P (P₀.pull φ₂o) → IsGrpPullback u.A A₀ πZ φu → IsSquare φu φ₂u → LBIso u.P (P₀.pull φ₂u) → z ≫ πZ = g → ψ ≫ φu = φo → ψ ≫ u.A.hom = o.A.hom ≫ z → (∀ a : D.O, (o.act.act a).left ≫ ψ = ψ ≫ (u.act.act a).left) → (∀ y, (o.eta y).left ≫ ψ = z ≫ (u.eta y).left) → ∃ m : ObjMap o u z, m.φ = ψ := by
  intro p _ D R _ b N S₀ A₀ _ P₀ hP₀ T Z t₁ t₂ o u g πZ z φo φ₂o φu φ₂u ψ ho sqo io hu squ iu hz hψ hw hact heta
  have cart : IsGrpPullback o.A u.A z ψ := IsGrpPullback.cancel hu (by rw [hz, hψ]; exact ho) hw
  have wc : ((fst o.A o.A).left ≫ ψ) ≫ u.A.hom = ((snd o.A o.A).left ≫ ψ) ≫ u.A.hom := by
    rw [Category.assoc, Category.assoc, hw, ← Category.assoc, ← Category.assoc, Over.w (fst o.A o.A), Over.w (snd o.A o.A)]
  let φ₂ : (G2 o.A).left ⟶ (G2 u.A).left := pullback.lift ((fst o.A o.A).left ≫ ψ) ((snd o.A o.A).left ≫ ψ) wc
  have s₁ : φ₂ ≫ (fst u.A u.A).left = (fst o.A o.A).left ≫ ψ := pullback.lift_fst _ _ _
  have s₂ : φ₂ ≫ (snd u.A u.A).left = (snd o.A o.A).left ≫ ψ := pullback.lift_snd _ _ _
  have sq : IsSquare ψ φ₂ := ⟨s₁, s₂⟩
  have a₁ : (φ₂ ≫ φ₂u) ≫ (fst A₀ A₀).left = φ₂o ≫ (fst A₀ A₀).left := by
    rw [Category.assoc, squ.1, ← Category.assoc, s₁, Category.assoc, hψ, sqo.1]
  have a₂ : (φ₂ ≫ φ₂u) ≫ (snd A₀ A₀).left = φ₂o ≫ (snd A₀ A₀).left := by
    rw [Category.assoc, squ.2, ← Category.assoc, s₂, Category.assoc, hψ, sqo.2]
  have e₂ : φ₂ ≫ φ₂u = φ₂o := Over.tensorObj_ext _ _ a₁ a₂
  have i₂ : LBIso (P₀.pull φ₂o) (u.P.pull φ₂) :=
    LBIso.chartPull (chartPullSame P₀ _ _ _ φ₂ (fun _ => e₂.symm)) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull u.P φ₂ φ₂ rfl) (LBIso.symm iu)
  have pol : LBIso o.P (u.P.pull φ₂) :=
    LBIso.trans o.isLB (pull_isLB hP₀ _) (pull_isLB u.isLB _) io i₂
  exact ⟨{ φ := ψ, φ₂ := φ₂, cart := cart, sq := sq, act := hact, pol := pol, eta := heta }, rfl⟩

end GlobalTheory.HTObjMap
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectMapOfCommonPullbackStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.exists_harrisTaylorObjectMap_of_common_pullback : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S₀ : Scheme.{0}) (A₀ : Over S₀) [GrpObj A₀] (P₀ : LB (G2 A₀).left), P₀.IsLB → ∀ (T Z : Scheme.{0}) (t₁ : T ⟶ Sp R) (t₂ : Z ⟶ Sp R) (o : Obj b N t₁) (u : Obj b N t₂) (g : T ⟶ S₀) (πZ : Z ⟶ S₀) (z : T ⟶ Z) (φo : o.A.left ⟶ A₀.left) (φ₂o : (G2 o.A).left ⟶ (G2 A₀).left) (φu : u.A.left ⟶ A₀.left) (φ₂u : (G2 u.A).left ⟶ (G2 A₀).left) (ψ : o.A.left ⟶ u.A.left), IsGrpPullback o.A A₀ g φo → IsSquare φo φ₂o → LBIso o.P (P₀.pull φ₂o) → IsGrpPullback u.A A₀ πZ φu → IsSquare φu φ₂u → LBIso u.P (P₀.pull φ₂u) → z ≫ πZ = g → ψ ≫ φu = φo → ψ ≫ u.A.hom = o.A.hom ≫ z → (∀ a : D.O, (o.act.act a).left ≫ ψ = ψ ≫ (u.act.act a).left) → (∀ y, (o.eta y).left ≫ ψ = z ≫ (u.eta y).left) → ∃ m : ObjMap o u z, m.φ = ψ := by
  first | (exact @GlobalTheory.HTObjMap.exists_objMap_of_common_pullback) | (exact GlobalTheory.HTObjMap.exists_objMap_of_common_pullback) | (intros; apply GlobalTheory.HTObjMap.exists_objMap_of_common_pullback  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieTateConditionsIffPullbacks

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.HTTransport

open ReciprocityTheory.ChartRestriction.G.Pdiv

variable {p : ℕ} [Fact p.Prime] {D : Datum p}

def tateTransport {k : Type} [Field k] {Q Q' : Type} [Group Q] [Group Q'] {act : D.O → Q → Q}
    {act' : D.O → Q' → Q'} {E : ℕ → Q → Q → kˣ → Prop} {E' : ℕ → Q' → Q' → kˣ → Prop}
    (I : TateIsoO D k Q act E) (e : Q ≃* Q') (ha : ∀ c g, e (act c g) = act' c (e g))
    (hE : ∀ n g g' u, E n g g' u → E' n (e g) (e g') u) : TateIsoO D k Q' act' E' where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev n y := e (I.ev n y)
  add n x y := by rw [I.add, map_mul]
  lin n c x := by rw [I.lin, ha]
  ker n hn hp x := by rw [map_eq_one_iff _ e.injective]; exact I.ker n hn hp x
  onto n hn hp q := by
    rw [← map_eq_one_iff e.symm e.symm.injective, map_pow, I.onto n hn hp]
    exact exists_congr fun y => ⟨fun h => by rw [h, e.apply_symm_apply], fun h => by rw [← h, e.symm_apply_apply]⟩
  tower n m hn hm hp x := by rw [← map_pow, I.tower n m hn hm hp]
  isom n hn hp x y := hE _ _ _ _ (I.isom n hn hp x y)

theorem exists_tate_iff {k : Type} [Field k] {Q Q' : Type} [Group Q] [Group Q'] {act : D.O → Q → Q}
    {act' : D.O → Q' → Q'} {E : ℕ → Q → Q → kˣ → Prop} {E' : ℕ → Q' → Q' → kˣ → Prop}
    (e : Q ≃* Q') (ha : ∀ c g, e (act c g) = act' c (e g))
    (hE : ∀ n g g' u, E n g g' u ↔ E' n (e g) (e g') u) (N : ℕ) (l : D.La → Q) (l' : D.La → Q')
    (hl : ∀ y, e (l y) = l' y) :
    (∃ I : TateIsoO D k Q act E, ∀ y, l y = I.ev N y) ↔ (∃ I : TateIsoO D k Q' act' E', ∀ y, l' y = I.ev N y) := by
  constructor
  · rintro ⟨I, hI⟩
    exact ⟨tateTransport I e ha fun n g g' u => (hE n g g' u).1, fun y => by rw [← hl, hI]; rfl⟩
  · rintro ⟨I, hI⟩
    refine ⟨tateTransport I e.symm (fun c g => e.injective (by rw [e.apply_symm_apply, ha, e.apply_symm_apply]))
      (fun n g g' u h => (hE n _ _ u).2 (by rw [e.apply_symm_apply, e.apply_symm_apply]; exact h)), fun y => ?_⟩
    show l y = e.symm (I.ev N y)
    rw [← hI y, ← hl y, e.symm_apply_apply]

variable {R : Type} [CommRing R] (b : Base D R) {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A]
  [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}

theorem lieAt_iff (pb : IsGrpPullback A' A f φ) (act : OActN D.O A) (act' : OActN D.O A')
    (hact : ∀ c, (act'.act c).left ≫ φ = φ ≫ (act.act c).left) {R' : Type} [CommRing R'] (β : R →+* R')
    (x : Sp R' ⟶ S') : LieAt b act' β x ↔ LieAt b act β (x ≫ f) := by
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv pb (epsPtR x) (spMap (algebraMap R' (DualNumber R')) ≫ x ≫ f)
    (Category.assoc _ _ _).symm
  have key := fun c r v => GlobalTheory.HTPull.isTanScal_iff pb act act' hact x e he c r v
  constructor
  · intro H v hv
    obtain ⟨w, hw, hvw⟩ := H (e.symm v) ((key _ _ _).2 (by rw [e.apply_symm_apply]; exact hv))
    refine ⟨fun i => e (w i), fun i c => (key _ _ _).1 (hw i c), ?_⟩
    rw [← e.apply_symm_apply v, hvw, map_list_prod, List.map_ofFn]
    rfl
  · intro H v hv
    obtain ⟨w, hw, hvw⟩ := H (e v) ((key _ _ _).1 hv)
    refine ⟨fun i => e.symm (w i), fun i c => (key _ _ _).2 (by rw [e.apply_symm_apply]; exact hw i c),
      e.injective ?_⟩
    rw [hvw, map_list_prod, List.map_ofFn]
    simp [Function.comp_def]

theorem lieRankAt_iff (pb : IsGrpPullback A' A f φ) (act : OActN D.O A) (act' : OActN D.O A')
    (hact : ∀ c, (act'.act c).left ≫ φ = φ ≫ (act.act c).left) {R' : Type} [CommRing R'] (β : R →+* R')
    (x : Sp R' ⟶ S') : LieRankAt b act' β x ↔ LieRankAt b act β (x ≫ f) := by
  refine forall_congr' fun k => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun g =>
    forall_congr' fun i => ?_
  have h := GlobalTheory.LiePull.lieMult_pull (𝓞 D.F) S S' A A' f φ (act.toF D) (act'.toF D) pb (fun c => hact _) k
    (spMap g ≫ x) ((g.comp β).comp (b.t i)) D.m
  rwa [Category.assoc] at h

theorem lieHer_iff (pb : IsGrpPullback A' A f φ) (act : OActN D.O A) (act' : OActN D.O A')
    (hact : ∀ c, (act'.act c).left ≫ φ = φ ≫ (act.act c).left) {R' : Type} [CommRing R'] (β : R →+* R')
    (x : Sp R' ⟶ S') : LieHer b act' β x ↔ LieHer b act β (x ≫ f) := by
  refine forall_congr' fun R'' => forall_congr' fun _ => forall_congr' fun g => ?_
  have h1 := lieAt_iff b pb act act' hact (g.comp β) (spMap g ≫ x)
  have h2 := lieRankAt_iff b pb act act' hact (g.comp β) (spMap g ≫ x)
  rw [Category.assoc] at h1 h2
  exact and_congr h1 h2

theorem geomAt_iff [IsCommMonObj A] (pb : IsGrpPullback A' A f φ) (act : OActN D.O A) (act' : OActN D.O A')
    (hact : ∀ c, (act'.act c).left ≫ φ = φ ≫ (act.act c).left) (P : LB (G2 A).left) (P' : LB (G2 A').left)
    (hP : P.IsLB) (hP' : P'.IsLB) (φ₂ : (G2 A').left ⟶ (G2 A).left) (sq : IsSquare φ φ₂)
    (H : LBIso P' (P.pull φ₂)) (eta : D.La → (𝟙_ (Over S) ⟶ A)) (eta' : D.La → (𝟙_ (Over S') ⟶ A'))
    (heta : ∀ y, (eta' y).left ≫ φ = f ≫ (eta y).left) (N : ℕ) (k : Type) [Field k] (x : Sp k ⟶ S') :
    GeomAt D N act' P' eta' k x ↔ GeomAt D N act P eta k (x ≫ f) := by
  have dg := SiegelPull.diag_iso sq H
  let e : (Over.mk x ⟶ A') ≃* (Over.mk (x ≫ f) ⟶ A) := MulEquiv.ofBijective (pushHom pb (Over.mk x))
    ⟨SiegelPull.push_injective pb _, SiegelPull.push_surjective pb _⟩
  have hel : ∀ g, (e g).left = g.left ≫ φ := fun g => rfl
  refine exists_tate_iff e (fun c g => GlobalTheory.HTPull.push_comp pb (hact c) _ g) (fun n g g' u => ?_) N _ _
    (fun y => ?_)
  · exact weilIs_grpPullback_of_comm S S' A A' f φ _ _ (pull_isLB hP _) (pull_isLB hP' _) pb dg (Over.mk x) n
      g g' (e g) (e g') _ (hel g) (hel g')
  · apply Over.OverMorphism.ext
    show ((toUnit (Over.mk x)).left ≫ (eta' y).left) ≫ φ = (toUnit (Over.mk (x ≫ f))).left ≫ (eta y).left
    rw [Category.assoc, heta, Over.toUnit_left, Over.toUnit_left, ← Category.assoc]
    rfl

end GlobalTheory.HTTransport

namespace GlobalTheory.HTTransport

open ReciprocityTheory.ChartRestriction.G.Pdiv

theorem lieHer_geomAt_iff : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S₀ : Scheme.{0}) (A₀ : Over S₀) [GrpObj A₀] [IsCommMonObj A₀] (P₀ : LB (G2 A₀).left), P₀.IsLB → ∀ (X T : Scheme.{0}) (πX : X ⟶ S₀) (z : T ⟶ X) (AX : Over X) [GrpObj AX] [IsCommMonObj AX] (AT : Over T) [GrpObj AT] [IsCommMonObj AT] (φX : AX.left ⟶ A₀.left) (φ₂X : (G2 AX).left ⟶ (G2 A₀).left) (φT : AT.left ⟶ A₀.left) (φ₂T : (G2 AT).left ⟶ (G2 A₀).left) (ψ : AT.left ⟶ AX.left) (actX : OActN D.O AX) (actT : OActN D.O AT) (ηX : D.La → (𝟙_ (Over X) ⟶ AX)) (ηT : D.La → (𝟙_ (Over T) ⟶ AT)) (PT : LB (G2 AT).left), PT.IsLB → IsGrpPullback AX A₀ πX φX → IsSquare φX φ₂X → IsGrpPullback AT A₀ (z ≫ πX) φT → IsSquare φT φ₂T → IsGrpPullback AT AX z ψ → ψ ≫ φX = φT → LBIso PT (P₀.pull φ₂T) → (∀ a : D.O, (actT.act a).left ≫ ψ = ψ ≫ (actX.act a).left) → (∀ y, (ηT y).left ≫ ψ = z ≫ (ηX y).left) → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ T), LieHer b actT β x ↔ LieHer b actX β (x ≫ z)) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T), GeomAt D N actT PT ηT k x ↔ GeomAt D N actX (P₀.pull φ₂X) ηX k (x ≫ z) := by
  intro p _ D R _ b N S₀ A₀ _ _ P₀ hP₀ X T πX z AX _ _ AT _ _ φX φ₂X φT φ₂T ψ actX actT ηX ηT PT hPT _ sqX _ sqT
    pbψ hψ H hact hη
  have w : ((fst AT AT).left ≫ ψ) ≫ AX.hom = ((snd AT AT).left ≫ ψ) ≫ AX.hom := by
    rw [Category.assoc, Category.assoc, pbψ.1.w, ← Category.assoc, ← Category.assoc, Over.w, Over.w]
  let ψ₂ : (G2 AT).left ⟶ (G2 AX).left := pullback.lift _ _ w
  have sqψ : IsSquare ψ ψ₂ := ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hcomp : ψ₂ ≫ φ₂X = φ₂T := by
    have h1 : (ψ₂ ≫ φ₂X) ≫ (fst A₀ A₀).left = φ₂T ≫ (fst A₀ A₀).left := by
      rw [Category.assoc, sqX.1, ← Category.assoc, sqψ.1, Category.assoc, hψ, sqT.1]
    have h2 : (ψ₂ ≫ φ₂X) ≫ (snd A₀ A₀).left = φ₂T ≫ (snd A₀ A₀).left := by
      rw [Category.assoc, sqX.2, ← Category.assoc, sqψ.2, Category.assoc, hψ, sqT.2]
    exact Over.tensorObj_ext _ _ h1 h2
  have hB : ((P₀.pull φ₂X).pull ψ₂).IsLB := pull_isLB (pull_isLB hP₀ _) _
  have iso : LBIso PT ((P₀.pull φ₂X).pull ψ₂) :=
    LBIso.trans hPT (pull_isLB hP₀ _) hB H
      (LBIso.chartPull (GlobalTheory.RigidBundleGlue.chartPullComp P₀ φ₂X ψ₂ φ₂T hcomp.symm) (chartPullId _)
        (PullbackComparison.gen_refl _ hB))
  exact ⟨fun R' _ β x => lieHer_iff b pbψ actX actT hact β x,
    fun k _ _ x => geomAt_iff pbψ actX actT hact (P₀.pull φ₂X) PT (pull_isLB hP₀ _) hPT ψ₂ sqψ iso ηX ηT hη N k x⟩

end GlobalTheory.HTTransport
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieTateConditionsIffPullbacksStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.harrisTaylorLie_tate_conditions_iff_pullbacks : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S₀ : Scheme.{0}) (A₀ : Over S₀) [GrpObj A₀] [IsCommMonObj A₀] (P₀ : LB (G2 A₀).left), P₀.IsLB → ∀ (X T : Scheme.{0}) (πX : X ⟶ S₀) (z : T ⟶ X) (AX : Over X) [GrpObj AX] [IsCommMonObj AX] (AT : Over T) [GrpObj AT] [IsCommMonObj AT] (φX : AX.left ⟶ A₀.left) (φ₂X : (G2 AX).left ⟶ (G2 A₀).left) (φT : AT.left ⟶ A₀.left) (φ₂T : (G2 AT).left ⟶ (G2 A₀).left) (ψ : AT.left ⟶ AX.left) (actX : OActN D.O AX) (actT : OActN D.O AT) (ηX : D.La → (𝟙_ (Over X) ⟶ AX)) (ηT : D.La → (𝟙_ (Over T) ⟶ AT)) (PT : LB (G2 AT).left), PT.IsLB → IsGrpPullback AX A₀ πX φX → IsSquare φX φ₂X → IsGrpPullback AT A₀ (z ≫ πX) φT → IsSquare φT φ₂T → IsGrpPullback AT AX z ψ → ψ ≫ φX = φT → LBIso PT (P₀.pull φ₂T) → (∀ a : D.O, (actT.act a).left ≫ ψ = ψ ≫ (actX.act a).left) → (∀ y, (ηT y).left ≫ ψ = z ≫ (ηX y).left) → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ T), LieHer b actT β x ↔ LieHer b actX β (x ≫ z)) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T), GeomAt D N actT PT ηT k x ↔ GeomAt D N actX (P₀.pull φ₂X) ηX k (x ≫ z) := by
  first | (exact @GlobalTheory.HTTransport.lieHer_geomAt_iff) | (exact GlobalTheory.HTTransport.lieHer_geomAt_iff) | (intros; apply GlobalTheory.HTTransport.lieHer_geomAt_iff  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorStructuresRelativelyRepresentable

section

@[expose] public section

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

theorem relRep_htPull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∃ (Z : Scheme.{0}) (π : Z ⟶ S) (u : Obj b N (π ≫ t)) (φu : u.A.left ⟶ c.A.left) (φ₂u : (G2 u.A).left ⟶ (G2 c.A).left), IsGrpPullback u.A c.A π φu ∧ IsSquare φu φ₂u ∧ LBIso u.P (c.P.pull φ₂u) ∧ IsFinite π ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S) (t' : T ⟶ Sp R) (o : Obj b N t') (φ : o.A.left ⟶ c.A.left) (φ₂ : (G2 o.A).left ⟶ (G2 c.A).left), g ≫ t = t' → IsGrpPullback o.A c.A g φ → IsSquare φ φ₂ → LBIso o.P (c.P.pull φ₂) → ∃! z : T ⟶ Z, z ≫ π = g ∧ ∃ m : ObjMap o u z, m.φ ≫ φu = φ := by
  intro p _ D R _ b N hN hNp h M B _ ζ S _ s₁ t c e he hc
  obtain ⟨E, πE, AE, _, _, φE, φ₂E, actE, ηE, hEn, hEf, pbE, sqE, rosE, etaE, univE⟩ :=
    GlobalTheory.T.exists_rep_adjointAction_level_siegelPullback p D R b N hNp h M B ζ S s₁ t c e he hc
  obtain ⟨Z, j, hj, hZ⟩ := GlobalTheory.T.harrisTaylor_lie_tate_loci_closed_siegelPullback p D R b N hN hNp h M B ζ S s₁ t c e he hc E πE AE φE φ₂E actE ηE
    pbE sqE rosE etaE
  have hZj := (hZ Z j).1 ⟨𝟙 Z, Category.id_comp _⟩
  obtain ⟨u, ψ, ψ₂, pbu, squ, isou, actu, etau⟩ := GlobalTheory.T.exists_harrisTaylorObject_over_lieTate_locus p D R b N hN hNp h M B ζ S s₁ t c e he hc E πE AE
    φE φ₂E actE ηE pbE sqE rosE etaE Z j hZj.1 hZj.2
  haveI : IsFinite πE := hEf
  haveI : Mono j := inferInstance
  refine ⟨Z, j ≫ πE, u, ψ ≫ φE, ψ₂, pbu.comp pbE, squ, isou, inferInstance, ?_⟩
  intro T g t' o φ φ₂ hgt pbo sqo isoo
  have rosO : RosatiFor D o.act (c.P.pull φ₂) :=
    RosatiFor.of_iso o.isLB (pull_isLB c.isLB _) isoo o.rosatiFor
  obtain ⟨z₀, ⟨hz₀, ψ₀, pb₀, hψ₀, act₀, eta₀⟩, uniq₀⟩ := univE T g o.A φ φ₂ o.act o.eta pbo sqo rosO o.etaOK
  have pbo' : IsGrpPullback o.A c.A (z₀ ≫ πE) φ := by rw [hz₀]; exact pbo
  have tr := GlobalTheory.T.harrisTaylorLie_tate_conditions_iff_pullbacks p D R b N S c.A c.P c.isLB E T πE z₀ AE o.A φE φ₂E φ φ₂ ψ₀ actE o.act ηE o.eta o.P
    o.isLB pbE sqE pbo' sqo pb₀ hψ₀ isoo act₀ eta₀
  have hpt : ∀ {R' : Type} [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ T), x ≫ z₀ ≫ πE ≫ t = spMap β →
      x ≫ t' = spMap β := fun β x hx => by
    rw [← hgt, ← hz₀]; simpa [Category.assoc] using hx
  obtain ⟨z, hz⟩ := (hZ T z₀).2 ⟨fun R' _ β x hx => (tr.1 R' β x).1 (o.lieHer R' β x (hpt β x hx)),
    fun k _ _ x β hx => (tr.2 k x).1 (o.geomAt k x β (hpt β x hx))⟩
  have w : ψ₀ ≫ AE.hom = (o.A.hom ≫ z) ≫ j := by rw [pb₀.1.w, Category.assoc, hz]
  let ψ' := pbu.1.lift ψ₀ (o.A.hom ≫ z) w
  have h1 : ψ' ≫ ψ = ψ₀ := pbu.1.lift_fst _ _ _
  have h2 : ψ' ≫ u.A.hom = o.A.hom ≫ z := pbu.1.lift_snd _ _ _
  have hact : ∀ a : D.O, (o.act.act a).left ≫ ψ' = ψ' ≫ (u.act.act a).left := fun a => by
    apply pbu.1.hom_ext
    · rw [Category.assoc, h1, act₀, Category.assoc, actu, ← Category.assoc, h1]
    · rw [Category.assoc, h2, Category.assoc, Over.w (u.act.act a), h2, ← Category.assoc,
        Over.w (o.act.act a)]
  have heta : ∀ y, (o.eta y).left ≫ ψ' = z ≫ (u.eta y).left := fun y => by
    apply pbu.1.hom_ext
    · rw [Category.assoc, h1, eta₀, Category.assoc, etau, ← Category.assoc, hz]
    · rw [Category.assoc, h2, Category.assoc, Over.w (u.eta y), ← Category.assoc, Over.w (o.eta y)]
      simp
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_harrisTaylorObjectMap_of_common_pullback p D R b N S c.A c.P c.isLB T Z t' ((j ≫ πE) ≫ t) o u g (j ≫ πE) z φ φ₂
    (ψ ≫ φE) ψ₂ ψ' pbo sqo isoo (pbu.comp pbE) squ isou (by rw [← Category.assoc, hz, hz₀])
    (by rw [← Category.assoc, h1, hψ₀]) h2 hact heta
  refine ⟨z, ⟨by rw [← Category.assoc, hz, hz₀], m, by rw [hm, ← Category.assoc, h1, hψ₀]⟩, ?_⟩
  rintro z' ⟨hz', m', hm'⟩
  have e₀ : z' ≫ j = z₀ := uniq₀ (z' ≫ j) ⟨by rw [Category.assoc]; exact hz', m'.φ ≫ ψ, m'.cart.comp pbu,
    by rw [Category.assoc]; exact hm',
    fun a => by rw [← Category.assoc, m'.act a, Category.assoc, actu]; exact (Category.assoc _ _ _).symm,
    fun y => by rw [← Category.assoc, m'.eta y, Category.assoc, etau]; exact (Category.assoc _ _ _).symm⟩
  exact (cancel_mono j).1 (e₀.trans hz.symm)

end GlobalTheory.UPel.HT
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorStructuresRelativelyRepresentableStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.harrisTaylor_structures_relatively_representable : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∃ (Z : Scheme.{0}) (π : Z ⟶ S) (u : Obj b N (π ≫ t)) (φu : u.A.left ⟶ c.A.left) (φ₂u : (G2 u.A).left ⟶ (G2 c.A).left), IsGrpPullback u.A c.A π φu ∧ IsSquare φu φ₂u ∧ LBIso u.P (c.P.pull φ₂u) ∧ IsFinite π ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S) (t' : T ⟶ Sp R) (o : Obj b N t') (φ : o.A.left ⟶ c.A.left) (φ₂ : (G2 o.A).left ⟶ (G2 c.A).left), g ≫ t = t' → IsGrpPullback o.A c.A g φ → IsSquare φ φ₂ → LBIso o.P (c.P.pull φ₂) → ∃! z : T ⟶ Z, z ≫ π = g ∧ ∃ m : ObjMap o u z, m.φ ≫ φu = φ := by
  first | (exact @GlobalTheory.UPel.HT.relRep_htPull) | (exact GlobalTheory.UPel.HT.relRep_htPull) | (intros; apply GlobalTheory.UPel.HT.relRep_htPull  <;> assumption)
end
end
