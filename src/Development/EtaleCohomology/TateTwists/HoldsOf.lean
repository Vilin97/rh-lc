module

public import Development.EtaleCohomology.TateTwists.EtaleInjectiveResolutionSectionsLocallyExact
public import Development.EtaleCohomology.TateTwists.EtaleKummerClassExplicitCocycle
public import Development.EtaleCohomology.TateTwists.EtaleKummerTriangleExists
public import Development.EtaleCohomology.TateTwists.EtalePrimitiveRootsExistLocally
public import Development.EtaleCohomology.TateTwists.Delta
public import Development.EtaleCohomology.TateTwists.EtaleChainCochainEvalBasicPropertiesHold
import Development.EtaleCohomology.TateTwists.EtaleChainCochainEvalDifferentialFormulaHolds
public import Development.EtaleCohomology.TateTwists.EtaleChainCochainExistsOfEvalData
public import Development.EtaleCohomology.TateTwists.EtaleLocallyExistsPrimitiveRootOfUnityOfInvertibleOrder
public import Development.EtaleCohomology.TateTwists.EtaleLocallyKummerRootsOfUnitsOfInvertibleOrder
public import Development.EtaleCohomology.TateTwists.EtaleSheafSectionsGlueOfForgetIsSheaf
import Development.EtaleCohomology.TateTwists.ExactLocPf
public import Development.EtaleCohomology.TateTwists.EtaleKummerClassSpecificationOfExistenceNaturali
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Development.EtaleCohomology.TateTwists.KumMulCocPf
public import Development.EtaleCohomology.TateTwists.KumAddPf
import Mathlib.Tactic.Lemma
public import Development.EtaleCohomology.TateTwists.EtaleLocallyExistsPrimitiveRootOfUnityOfInvertib

-- Source module: Development.EtaleCohomology.TateTwists.KumExistsPf

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def L_kumT_ex : Prop := ∀ (q : ℕ) [NeZero q], IsKum q (kumT q)

def L_prim_loc : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), (IsUnit (q : Γ(U, ⊤)) → Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))) ∧ (∀ ζ ξ : Prim q Γ(U, ⊤), Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val) ∧ (∀ (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤)), x ^ q = 1 → Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a) ∧ (IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ, Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u)

def L_sec_glue : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ a b : Sec F U, (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b) ∧ ∀ (S : Sieve U), S ∈ Scheme.etaleTopology U → ∀ s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec F V, (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g), Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k)) → ∃ a : Sec F U, ∀ V g hg, Sec.res g a = s V g hg

def L_sch_cls : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (I : Cx R) (m n k : ℤ), m + 1 = n → n + 1 = k → (∀ z : Sec (I.X n) X, Sec.map (I.d n k) z = 0 → ∃ α : Cocycle ((chains R).obj (sch.obj X)) I n, (∀ (U : Scheme.{0}) (x : U ⟶ X), ev α.1 0 n (by simp) U x = Sec.res x z) ∧ ∀ (p : ℕ) s h U x, ev α.1 (p + 1) s h U x = 0) ∧ ∀ α : Cocycle ((chains R).obj (sch.obj X)) I n, Sec.map (I.d n k) (ev α.1 0 n (by simp) X (𝟙 X)) = 0 ∧ (CohomologyClass.mk α = 0 ↔ ∃ y : Sec (I.X m) X, Sec.map (I.d m n) y = ev α.1 0 n (by simp) X (𝟙 X))

def L_res_sec : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ z : Sec ((res R F).X 0) U, Sec.map ((res R F).d 0 1) z = 0 ↔ ∃ a : Sec F U, Sec.map (resι R F) a = z) ∧ Function.Injective (Sec.map (resι R F) (U := U)) ∧ (∀ (m n k : ℤ), 0 < n → m + 1 = n → ∀ z : Sec ((res R F).X n) U, n + 1 = k → Sec.map ((res R F).d n k) z = 0 → Loc U fun V g => ∃ y : Sec ((res R F).X m) V, Sec.map ((res R F).d m n) y = Sec.res g z) ∧ ∀ n : ℤ, n < 0 → Subsingleton (Sec ((res R F).X n) U)

section Basic
variable {R : Type} [CommRing R]

theorem sec_res_map {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  (ConcreteCategory.congr_hom (φ.hom.naturality g.op) x).symm

theorem sec_res_comp {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  show (F.obj.map (k ≫ g).op).hom x = (F.obj.map k.op).hom ((F.obj.map g.op).hom x)
  rw [op_comp, Functor.map_comp]
  rfl

theorem sec_res_zero {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec F U) = 0 := map_zero _

theorem sec_map_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem sec_map_add {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x + y) = Sec.map φ x + Sec.map φ y := LinearMap.map_add _ _ _

theorem sec_map_zero {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (0 : F ⟶ G) x = 0 := by
  simp [Sec.map]

end Basic

theorem prim_pow {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨p, hp⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (Polynomial.aeval ζ.1) hp
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, ζ.2.2, zero_mul] at h
  exact sub_eq_zero.mp h

theorem prim_isUnit {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) : IsUnit ζ.1 :=
  IsUnit.of_pow_eq_one (prim_pow ζ) (NeZero.ne q)

theorem units_root {q : ℕ} {X U V : Scheme.{0}} (u : (Γ(X, ⊤))ˣ) (x : U ⟶ X) (g : V ⟶ U) (w : (Γ(U, ⊤))ˣ)
    (h : w ^ q = Units.map x.appTop.hom.toMonoidHom u) :
    (Units.map g.appTop.hom.toMonoidHom w) ^ q = Units.map (g ≫ x).appTop.hom.toMonoidHom u := by
  rw [← map_pow, h]
  ext
  simp
  rfl

section Kum
variable (q : ℕ) [NeZero q]

theorem d_resGen (hR : L_res_sec) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) :
    Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (resGen 1 ζ) = 0 :=
  ((hR (ZMod q) (tw q 1) U).1 _).2 ⟨twGen 1 ζ, rfl⟩

theorem dt_pow (hK : L_kumT_ex) (hR : L_res_sec) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (a : ℕ) :
    ∀ v w : (Γ(U, ⊤))ˣ, (w : Γ(U, ⊤)) = ζ.1 ^ a * v →
      Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q U w) = Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q U v) := by
  induction a with
  | zero =>
    intro v w h
    have : w = v := Units.ext (by simpa using h)
    subst this; rfl
  | succ a ih =>
    intro v w h
    let m : (Γ(U, ⊤))ˣ := (prim_isUnit ζ).unit ^ a * v
    have hm : (m : Γ(U, ⊤)) = ζ.1 ^ a * v := by simp [m]
    have hw : (w : Γ(U, ⊤)) = ζ.1 * m := by rw [h, hm, pow_succ]; ring
    rw [(hK q).2 U ζ m w hw, sec_map_add, d_resGen q hR, add_zero]
    exact ih v m hm

theorem dt_root (hK : L_kumT_ex) (hP : L_prim_loc) (hG : L_sec_glue) (hR : L_res_sec) {W : Scheme.{0}}
    (hqW : IsUnit (q : Γ(W, ⊤))) (w1 w2 : (Γ(W, ⊤))ˣ) (h : w1 ^ q = w2 ^ q) :
    Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q W w1) = Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q W w2) := by
  let ρ : (Γ(W, ⊤))ˣ := w2 * w1⁻¹
  have hρ : ρ ^ q = 1 := by
    simp only [ρ]; rw [mul_pow, inv_pow, ← h, mul_inv_cancel]
  apply (hG (ZMod q) _ W).1
  obtain ⟨S, hS, hPS⟩ := (hP q W).1 hqW
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨ζ⟩ := hPS V g hg
  have hqV : IsUnit (q : Γ(V, ⊤)) := by simpa using hqW.map g.appTop.hom
  have hr : (g.appTop.hom (ρ : Γ(W, ⊤))) ^ q = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hρ, Units.val_one, map_one]
  rw [sec_res_map, sec_res_map, (hK q).1 V W g w1 hqW, (hK q).1 V W g w2 hqW]
  apply (hG (ZMod q) _ V).1
  obtain ⟨T, hT, hPT⟩ := (hP q V).2.2.1 ζ _ hr
  refine ⟨T, hT, fun V' k hk => ?_⟩
  dsimp only
  obtain ⟨a, ha⟩ := hPT V' k hk
  rw [sec_res_map, sec_res_map, (hK q).1 V' V k _ hqV, (hK q).1 V' V k _ hqV]
  symm
  apply dt_pow q hK hR (Prim.map k.appTop.hom ζ) a
  have e : (w2 : Γ(W, ⊤)) = (ρ : Γ(W, ⊤)) * w1 := by simp [ρ]
  change k.appTop.hom (g.appTop.hom (w2 : Γ(W, ⊤))) = (k.appTop.hom ζ.1) ^ a * k.appTop.hom (g.appTop.hom (w1 : Γ(W, ⊤)))
  rw [e, map_mul, map_mul, ha]

end Kum

theorem kum_exists_of (hK : L_kumT_ex) (hP : L_prim_loc) (hG : L_sec_glue) (hC : L_sch_cls) (hR : L_res_sec) :
    kum_exists := by
  intro q _ X u hq
  have hqU : ∀ {U : Scheme.{0}} (x : U ⟶ X), IsUnit (q : Γ(U, ⊤)) := fun x => by simpa using hq.map x.appTop.hom
  have key : ∀ {U : Scheme.{0}} (x : U ⟶ X) (w1 w2 : (Γ(U, ⊤))ˣ), w1 ^ q = Units.map x.appTop.hom.toMonoidHom u →
      w2 ^ q = Units.map x.appTop.hom.toMonoidHom u →
      Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q U w1) = Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q U w2) :=
    fun x w1 w2 h1 h2 => dt_root q hK hP hG hR (hqU x) w1 w2 (h1.trans h2.symm)
  obtain ⟨S, hS, hroot⟩ := (hP q X).2.2.2 hq u
  choose v hv using hroot
  obtain ⟨z, hz⟩ := (hG (ZMod q) ((res (ZMod q) (tw q 1)).X 1) X).2 S hS
    (fun V g hg => Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q V (v V g hg))) (by
      intro V W g k hg
      rw [sec_res_map, (hK q).1 W V k _ (hqU g)]
      exact key (k ≫ g) _ _ (units_root u g k _ (hv V g hg)) (hv W (k ≫ g) _))
  have hdz : Sec.map ((res (ZMod q) (tw q 1)).d 1 2) z = 0 := by
    apply (hG (ZMod q) _ X).1
    refine ⟨S, hS, fun V g hg => ?_⟩
    dsimp only
    rw [sec_res_map, hz V g hg, sec_res_zero, ← sec_map_comp, HomologicalComplex.d_comp_d, sec_map_zero]
  obtain ⟨α, hα0, hα1⟩ := (hC (ZMod q) X (res (ZMod q) (tw q 1)) 0 1 2 (by norm_num) (by norm_num)).1 z hdz
  refine ⟨α, fun U x => hα1 0 0 _ U x, fun U x w hw => ?_⟩
  rw [hα0 U x]
  apply (hG (ZMod q) _ U).1
  refine ⟨S.pullback x, (Scheme.etaleTopology).pullback_stable x hS, fun V g hg => ?_⟩
  dsimp only
  rw [← sec_res_comp, hz V (g ≫ x) hg, sec_res_map, (hK q).1 V U g w (hqU x)]
  exact key (g ≫ x) _ _ (hv V (g ≫ x) hg) (units_root u x g w hw)

end LateralTheory.EtaleFoundations
end
end

-- Source module: Development.EtaleCohomology.TateTwists.KumNatPf

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def ev_basic : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, (∀ (α β : Cochain ((chains R).obj E) I n) p s h U x, ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x ∧ ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x ∧ ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 ∧ ∀ c : ℤ, ev (c • α) p s h U x = c • ev α p s h U x) ∧ (∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (ev α p s h U x) = ev α p s h V (x.res g)) ∧ (∀ α β : Cochain ((chains R).obj E) I n, (∀ p s h U x, ev α p s h U x = ev β p s h U x) → α = β) ∧ (∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U), ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f)) ∧ ∀ {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x, ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x)

def prim_loc : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), (IsUnit (q : Γ(U, ⊤)) → Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))) ∧ (∀ ζ ξ : Prim q Γ(U, ⊤), Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val) ∧ (∀ (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤)), x ^ q = 1 → Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a) ∧ (IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ, Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u)

def sec_glue : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ a b : Sec F U, (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b) ∧ ∀ (S : Sieve U), S ∈ Scheme.etaleTopology U → ∀ s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec F V, (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g), Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k)) → ∃ a : Sec F U, ∀ V g hg, Sec.res g a = s V g hg

theorem res_neg_isZero (R : Type) [CommRing R] (F : Shv R) (s : ℤ) (hs : s < 0) : IsZero ((res R F).X s) := by
  unfold res InjectiveResolution.cochainComplex
  exact HomologicalComplex.isZero_extend_X _ _ _ (by intro i h; change ((i : ℕ) : ℤ) = s at h; omega)

theorem units_map_comp {V U X : Scheme.{0}} (g : V ⟶ U) (x : U ⟶ X) (u : (Γ(X, ⊤))ˣ) :
    Units.map (g ≫ x).appTop.hom.toMonoidHom u =
      Units.map g.appTop.hom.toMonoidHom (Units.map x.appTop.hom.toMonoidHom u) := by
  ext; simp; rfl

theorem isUnit_q_map {U X : Scheme.{0}} (x : U ⟶ X) (q : ℕ) (hq : IsUnit (q : Γ(X, ⊤))) :
    IsUnit (q : Γ(U, ⊤)) := by
  simpa using hq.map x.appTop.hom

theorem kum_unique (hev : ev_basic) (hpl : prim_loc) (hsg : sec_glue) (q : ℕ) [NeZero q] (X : Scheme.{0})
    (u : (Γ(X, ⊤))ˣ) (hq : IsUnit (q : Γ(X, ⊤)))
    (γ γ' : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1)
    (h1 : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ.1 1 0 (by simp) U x = 0)
    (h2 : ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u →
        ev γ.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v))
    (h1' : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ'.1 1 0 (by simp) U x = 0)
    (h2' : ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u →
        ev γ'.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) : γ = γ' := by
  apply Cocycle.ext
  apply (hev (ZMod q)).2.2.1
  intro p s h U x
  match p, s, h with
  | 0, s, h =>
    obtain rfl : s = 1 := by omega
    revert x
    show ∀ x : U ⟶ X, _
    intro x
    apply (hsg (ZMod q) _ U).1
    obtain ⟨S, hS, hroot⟩ := (hpl q U).2.2.2 (isUnit_q_map x q hq) (Units.map x.appTop.hom.toMonoidHom u)
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨v, hv⟩ := hroot V g hg
    have hv' : v ^ q = Units.map (g ≫ x).appTop.hom.toMonoidHom u := by rw [units_map_comp]; exact hv
    exact ((hev (ZMod q)).2.1 γ.1 0 1 h V U g x).trans ((h2 V (g ≫ x) v hv').trans
      ((h2' V (g ≫ x) v hv').symm.trans ((hev (ZMod q)).2.1 γ'.1 0 1 h V U g x).symm))
  | 1, s, h =>
    obtain rfl : s = 0 := by omega
    exact (h1 U x).trans (h1' U x).symm
  | p + 2, s, h =>
    have hz := res_neg_isZero (ZMod q) (tw q 1) s (by omega)
    have hv : γ.1.v (-((p + 2 : ℕ) : ℤ)) s h = γ'.1.v (-((p + 2 : ℕ) : ℤ)) s h := hz.eq_of_tgt _ _
    unfold ev
    rw [hv]

theorem kum_nat_of (he : kum_exists) (hev : ev_basic) (hpl : prim_loc) (hsg : sec_glue) : kum_nat := by
  intro q _ Y X f u hq
  obtain ⟨γ, hc, h1, h2⟩ := kum_spec_of_exists he q X u hq
  have hqY := isUnit_q_map f q hq
  obtain ⟨γ', hc', h1', h2'⟩ := kum_spec_of_exists he q Y (Units.map f.appTop.hom.toMonoidHom u) hqY
  rw [← hc, ← hc']
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (sch.map f))) γ (zero_add 1)) = _
  congr 1
  refine kum_unique hev hpl hsg q Y _ hqY _ γ' ?_ ?_ h1' h2'
  · intro U x
    exact ((hev (ZMod q)).2.2.2.1 (sch.map f) γ.1 1 0 (by simp) U x).trans (h1 U (x ≫ f))
  · intro U x v hv
    exact ((hev (ZMod q)).2.2.2.1 (sch.map f) γ.1 0 1 (by simp) U x).trans
      (h2 U (x ≫ f) v (by rw [hv, units_map_comp]))

end LateralTheory.EtaleFoundations
end
end

-- Source module: Development.EtaleCohomology.TateTwists.KumPowCocPf

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

abbrev LkumTex : Prop := ∀ (q : ℕ) [NeZero q], IsKum q (kumT q)

abbrev LevMk : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
  (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U),
  (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) →
  ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev α p s h U x = a p s h U x

abbrev LevDelta : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m)
  (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}),
  (∀ (x : Sx E 0 U), ev (δ n m α) 0 m (by simp) U x = Sec.map (I.d n m) (ev α 0 n (by simp) U x)) ∧
  ∀ (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U),
    ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) +
      m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U (x.face i)

lemma units_map_appTop_comp {V U X : Scheme.{0}} (g : V ⟶ U) (x : U ⟶ X) (u : (Γ(X, ⊤))ˣ) :
    Units.map g.appTop.hom.toMonoidHom (Units.map x.appTop.hom.toMonoidHom u) =
      Units.map (g ≫ x).appTop.hom.toMonoidHom u := by
  ext; simp; rfl

lemma isUnit_q_pull {U X : Scheme.{0}} (q : ℕ) (x : U ⟶ X) (hq : IsUnit (q : Γ(X, ⊤))) :
    IsUnit (q : Γ(U, ⊤)) := by
  simpa using hq.map x.appTop.hom

theorem kum_pow_coc_of (hk : LkumTex) (hmk : LevMk) (hd : LevDelta) (he : kum_exists) : kum_pow_coc := by
  intro q _ X u hq
  let I := res _ (tw q 1)
  let a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + 0 = s → ∀ U : Scheme.{0}, Sx (sch.obj X) p U → Sec (I.X s) U :=
    fun p s _ U x => if hs : s = 0 then (by subst hs; exact kumT q U (Units.map (x : U ⟶ X).appTop.hom.toMonoidHom u))
      else 0
  have ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx (sch.obj X) p U),
      Sec.res g (a p s h U x) = a p s h V (x.res g) := by
    intro p s h V U g x
    by_cases hs : s = 0
    · subst hs
      simp only [a, dif_pos]
      rw [(hk q).1 V U g _ (isUnit_q_pull q x hq)]
      exact congrArg (kumT q V) (units_map_appTop_comp g x u)
    · simp only [a, dif_neg hs, map_zero]
  obtain ⟨α, hα⟩ := hmk (ZMod q) a ha
  refine ⟨Cocycle.mk (δ 0 1 α) 2 (by norm_num) (δ_δ 0 1 2 α), ⟨?_, ?_⟩, ?_⟩
  · have key : ∀ (U : Scheme.{0}) (x : Sx (sch.obj X) (0 + 1) U), ev (δ 0 1 α) (0 + 1) 0 (by simp) U x = 0 := by
      intro U x
      rw [(hd (ZMod q) (n := 0) (m := 1) (by norm_num) α U).2 0 (-1) 0 (by simp) (by simp) x, hα]
      have z : a (0 + 1) (-1) (by simp) U x = 0 := dif_neg (by norm_num)
      have f0 : x.face 0 = x.face 1 := rfl
      rw [z, Fin.sum_univ_two, f0]
      simp [Sec.map]
    exact fun U x => key U x
  · intro U x v hv
    obtain ⟨γ0, _, hγ0⟩ := he q X (u ^ q) hq
    have e1 := hγ0 U x v hv
    have e2 := hγ0 U x (Units.map x.appTop.hom.toMonoidHom u) (by rw [map_pow])
    have h1 := (hd (ZMod q) (n := 0) (m := 1) (by norm_num) α U).1 x
    refine h1.trans ?_
    erw [hα]
    simp only [a, dif_pos]
    exact e2.symm.trans e1
  · rw [CohomologyClass.mk_eq_zero_iff]
    exact ⟨0, by norm_num, α, rfl⟩

end LateralTheory.EtaleFoundations
end
end

-- Source module: Development.EtaleCohomology.TateTwists.KumUniqPf

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def uniq_prim_loc : Prop :=
  ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), (IsUnit (q : Γ(U, ⊤)) → Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))) ∧ (∀ ζ ξ : Prim q Γ(U, ⊤), Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val) ∧ (∀ (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤)), x ^ q = 1 → Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a) ∧ (IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ, Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u)

def sections_unique_of_local_agreement : Prop :=
  ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ a b : Sec F U, (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b) ∧ ∀ (S : Sieve U), S ∈ Scheme.etaleTopology U → ∀ s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec F V, (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g), Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k)) → ∃ a : Sec F U, ∀ V g hg, Sec.res g a = s V g hg

def uniq_ev_basic : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, (∀ (α β : Cochain ((chains R).obj E) I n) p s h U x, ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x ∧ ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x ∧ ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 ∧ ∀ c : ℤ, ev (c • α) p s h U x = c • ev α p s h U x) ∧ (∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (ev α p s h U x) = ev α p s h V (x.res g)) ∧ (∀ α β : Cochain ((chains R).obj E) I n, (∀ p s h U x, ev α p s h U x = ev β p s h U x) → α = β) ∧ (∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U), ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f)) ∧ ∀ {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x, ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x)

theorem sec_neg_eq (q : ℕ) [NeZero q] (s : ℤ) (hs : s < 0) (U : Scheme.{0})
    (a b : Sec ((res _ (tw q 1)).X s) U) : a = b := by
  have h0 : IsZero ((res _ (tw q 1)).X s) := by
    unfold res
    exact CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by omega)
  have h1 : IsZero (((res _ (tw q 1)).X s).obj.obj (op U)) :=
    ((sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op U)).map_isZero h0)
  have : Subsingleton (((res _ (tw q 1)).X s).obj.obj (op U)) :=
    (ModuleCat.isZero_iff_subsingleton).mp h1
  exact Subsingleton.elim a b

theorem root_res (q : ℕ) (X U V : Scheme.{0}) (u : (Γ(X, ⊤))ˣ) (x : U ⟶ X) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ)
    (hv : v ^ q = Units.map g.appTop.hom.toMonoidHom (Units.map x.appTop.hom.toMonoidHom u)) :
    v ^ q = Units.map (Sx.res (E := sch.obj X) (p := 0) g x : V ⟶ X).appTop.hom.toMonoidHom u := by
  have e : (Sx.res (E := sch.obj X) (p := 0) g x : V ⟶ X) = g ≫ x := rfl
  rw [hv, e]; ext; simp
  rfl

theorem kum_uniq_of (hl : uniq_prim_loc) (hg : sections_unique_of_local_agreement) (hb : uniq_ev_basic) : kum_uniq := by
  intro q _ X u hq γ γ' h h'
  have key : γ = γ' := by
    apply Subtype.ext
    apply (hb (ZMod q)).2.2.1
    intro p s hs U x
    rcases p with _ | _ | p
    · have hs' : s = 1 := by omega
      subst hs'
      have hqU : IsUnit ((q : ℕ) : Γ(U, ⊤)) := by
        have := hq.map x.appTop.hom
        simpa using this
      obtain ⟨S, hS, hP⟩ := (hl q U).2.2.2 hqU (Units.map x.appTop.hom.toMonoidHom u)
      apply (hg (ZMod q) _ U).1
      refine ⟨S, hS, fun V g hgS => ?_⟩
      obtain ⟨v, hv⟩ := hP V g hgS
      rw [(hb (ZMod q)).2.1, (hb (ZMod q)).2.1]
      have hv' := root_res q X U V u x g v hv
      rw [h.2 V _ v hv', h'.2 V _ v hv']
    · have hs' : s = 0 := by omega
      subst hs'
      rw [h.1 U x, h'.1 U x]
    · exact sec_neg_eq q s (by omega) U _ _
  rw [key]

end LateralTheory.EtaleFoundations
end
end

-- Source module: Development.EtaleCohomology.TateTwists.HoldsOf

section

@[expose] public section

namespace LateralTheory.Fix.EtaleKummerClassExplicitCocycle
open LateralTheory.EtaleFoundations

theorem primLoc : EtalePrimitiveRootsExistLocally := etale_locally_roots_of_unity_structure_of_exists_and_kummer etale_locally_exists_primitive_root_of_unity_of_invertible_order etale_locally_kummer_roots_of_units_of_invertible_order
theorem resSec : EtaleInjectiveResolutionSectionsLocallyExact := etaleSheaf_injectiveResolution_sections_exact_of_local_exactness LateralTheory.EtaleFoundations.ResSecPf.exact_loc_of

theorem holds_of (hK : EtaleKummerTriangleExists) : EtaleKummerClassExplicitCocycle := by
  have he : kum_exists := kum_exists_of hK primLoc etale_sheaf_sections_glue_of_forget_isSheaf LateralTheory.Fix.EtaleSchemeGlobalSectionCohomologyClass.intersectionNumber_baseChange resSec
  exact etale_kummer_class_specification_of_existence_naturality_additivity he
    (kum_nat_of he etale_chain_cochain_eval_basic_properties_hold primLoc etale_sheaf_sections_glue_of_forget_isSheaf)
    (kum_add_of he (kum_uniq_of primLoc etale_sheaf_sections_glue_of_forget_isSheaf etale_chain_cochain_eval_basic_properties_hold)
      (kum_mul_coc_of hK primLoc etale_sheaf_sections_glue_of_forget_isSheaf etale_chain_cochain_exists_of_eval_data etale_chain_cochain_eval_differential_formula_holds etale_chain_cochain_eval_basic_properties_hold)
      (kum_pow_coc_of hK etale_chain_cochain_exists_of_eval_data etale_chain_cochain_eval_differential_formula_holds he))

end LateralTheory.Fix.EtaleKummerClassExplicitCocycle
end
end
