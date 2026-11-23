module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EigenvectorLieDegree
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ThetaMove
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCmUnitaryShimuraMemClosureLinearHomImagesStatement

-- Source module: Development.AbelianVarietyTheory.Counterexamples.JetSurvey.PairingIsoPullback

section

@[expose] public section

noncomputable section

namespace GlobalTheory.LevelRigid

section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj


variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {c : Coeff l}

end
section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L)


end
section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

theorem pairing_weilMove (hW : Out.WeilSt) {S S' X : Scheme.{0}} [IsLocallyNoetherian S'] (hX : Subsingleton X)
    {G : Over S} [GrpObj G] {L₀ : LB G.left} (hL₀ : L₀.IsLB) (P₁ : Out.PolAV S') {f : S' ⟶ S}
    {φ : P₁.A.left ⟶ G.left} (hp : IsGrpPullback P₁.A G f φ) (w : LB.Iso P₁.L (L₀.pull φ)) (hw : w.IsGen)
    {tS : X ⟶ S'} {t₀ : X ⟶ S} (ht : t₀ = tS ≫ f) (n : ℕ) (x y : Over.mk tS ⟶ P₁.A) (hx : x ^ n = 1)
    (hy : y ^ n = 1) (x₀ y₀ : Over.mk t₀ ⟶ G) (hx₀ : x₀.left = x.left ≫ φ) (hy₀ : y₀.left = y.left ≫ φ)
    (c : Γ(X, ⊤)ˣ) (hG : Out.WeilIs G L₀ n x₀ y₀ c) : Out.WeilIs P₁.A P₁.L n x y c := by
  obtain ⟨c', hc', -⟩ := (hW S' P₁ n (Over.mk tS)).1 x y hx hy
  intro p
  obtain ⟨V, hpV, ⟨θx₀, θy₀, hpx₀, hpy₀⟩, hall₀⟩ := hG p
  obtain ⟨V', hpV', -, hall'⟩ := hc' p
  have hVV : V = V' := by
    ext q
    rw [@Subsingleton.elim _ hX q p]
    exact ⟨fun _ => hpV', fun _ => hpV⟩
  subst hVV
  have hτ : 𝟙 _ ≫ (Out.overRes (T := Over.mk t₀) V).hom = (Out.overRes (T := Over.mk tS) V).hom ≫ f := by
    rw [Category.id_comp]
    show V.ι ≫ t₀ = (V.ι ≫ tS) ≫ f
    rw [ht, Category.assoc]
  have mvx : 𝟙 _ ≫ θx₀.pt.left = (Out.overResι (T := Over.mk tS) V ≫ x).left ≫ φ := by
    rw [hpx₀, Category.id_comp, Over.comp_left, Over.comp_left, Category.assoc, hx₀]; rfl
  have mvy : 𝟙 _ ≫ θy₀.pt.left = (Out.overResι (T := Over.mk tS) V ≫ y).left ≫ φ := by
    rw [hpy₀, Category.id_comp, Over.comp_left, Over.comp_left, Category.assoc, hy₀]; rfl
  obtain ⟨θx, hθx, mx⟩ := H1.exists_theta_move (T := Out.overRes (T := Over.mk tS) V)
    (T₀ := Out.overRes (T := Over.mk t₀) V) hp (𝟙 _) hτ hL₀ P₁.isLB w hw n _ θx₀ mvx
  obtain ⟨θy, hθy, my⟩ := H1.exists_theta_move (T := Out.overRes (T := Over.mk tS) V)
    (T₀ := Out.overRes (T := Over.mk t₀) V) hp (𝟙 _) hτ hL₀ P₁.isLB w hw n _ θy₀ mvy
  have hm := H1.commIsOf_move (T := Out.overRes (T := Over.mk tS) V) (T₀ := Out.overRes (T := Over.mk t₀) V) hp
    (𝟙 _) hτ hL₀ P₁.isLB w n θx₀ θy₀ θx θy (by rw [hθx]; exact mvx) (by rw [hθy]; exact mvy) mx my
    (Out.unitRes (T := Over.mk t₀) V c) (Out.unitRes (T := Over.mk tS) V c)
    (fun Z r z => by rw [Category.comp_id]; rfl) (hall₀ θx₀ θy₀ hpx₀ hpy₀)
  have hcc := H1.commIsOf_unique P₁.isLB θx θy _ _ hm (hall' θx θy hθx hθy)
  refine ⟨V, hpV, ⟨θx, θy, hθx, hθy⟩, fun θx' θy' h₁ h₂ => ?_⟩
  rw [hcc]
  exact hall' θx' θy' h₁ h₂

theorem pairing_nondeg (hW : Out.WeilSt) (hND : Out.WeilNondegSt) (hBC : Out.PolBaseChangeSt)
    {S : Scheme.{0}} (B : Out.PolAV S) (F : Type) [Field F] [IsAlgClosed F]
    (t : Spec (CommRingCat.of F) ⟶ S) (n : ℕ) (hn : (n : F) ≠ 0) (u : Over.mk t ⟶ B.A)
    (hu : u ^ n = 1) (h : ∀ z : Over.mk t ⟶ B.A, z ^ n = 1 → Out.WeilIs B.A B.L n u z 1) : u = 1 := by
  obtain ⟨P', g, hg, -, hmul, tw, htw⟩ := hBC S (Spec (CommRingCat.of F)) t B
  obtain ⟨w, hw⟩ := LBIso.symm ⟨tw, htw⟩
  have hp : IsGrpPullback P'.A B.A t g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    rw [show x₀ = Out.toBase hg.w x from Over.OverMorphism.ext hx,
      show y₀ = Out.toBase hg.w y from Over.OverMorphism.ext hy, ← hmul]
    rfl⟩
  let i : Over.mk ((Out.baseOver (Spec (CommRingCat.of F))).hom ≫ t) ⟶ Over.mk t :=
    Over.homMk (𝟙 _) (by simp)
  have hi : ∀ a b : Over.mk t ⟶ B.A, i ≫ a = i ≫ b → a = b := fun a b hab => by
    apply Over.OverMorphism.ext
    have := congrArg CommaMorphism.left hab
    simpa [i] using this
  have tb1 : Out.toBase hg.w (1 : Out.baseOver _ ⟶ P'.A) = 1 := by
    have e := hmul (Out.baseOver _) 1 1
    rw [_root_.one_mul] at e
    exact mul_left_cancel (a := Out.toBase hg.w (1 : Out.baseOver _ ⟶ P'.A)) (by rw [_root_.mul_one]; exact e.symm)
  have tbpow : ∀ (z : Out.baseOver _ ⟶ P'.A) (m : ℕ), Out.toBase hg.w (z ^ m) = Out.toBase hg.w z ^ m := by
    intro z m
    induction m with
    | zero => rw [pow_zero, pow_zero, tb1]
    | succ m ih => rw [pow_succ, hmul, ih, pow_succ]
  let push : (Out.baseOver (Spec (CommRingCat.of F)) ⟶ P'.A) → (Over.mk t ⟶ B.A) := fun z =>
    Over.homMk (z.left ≫ g) (by
      show (z.left ≫ g) ≫ B.A.hom = t
      rw [Category.assoc, hg.w, ← Category.assoc, Over.w z]; simp)
  have tbpush : ∀ z, Out.toBase hg.w z = i ≫ push z := fun z =>
    Over.OverMorphism.ext (by simp [i, push, Out.toBase])
  have pinj : ∀ a b : Out.baseOver (Spec (CommRingCat.of F)) ⟶ P'.A, a.left ≫ g = b.left ≫ g → a = b :=
    fun a b hab => Over.OverMorphism.ext (hg.hom_ext hab (by rw [Over.w a, Over.w b]))
  let u' : Out.baseOver (Spec (CommRingCat.of F)) ⟶ P'.A :=
    Over.homMk (hg.lift u.left (𝟙 _) (by rw [Over.w u]; simp)) (hg.lift_snd _ _ _)
  have hu'g : u'.left ≫ g = u.left := hg.lift_fst _ _ _
  have hpu : push u' = u := Over.OverMorphism.ext hu'g
  have hu' : u' ^ n = 1 := by
    apply pinj
    have e : Out.toBase hg.w (u' ^ n) = Out.toBase hg.w 1 := by
      rw [tbpow, tb1, tbpush, hpu, ← MonObj.comp_pow, hu, MonObj.comp_one]
    exact congrArg CommaMorphism.left e
  have hall : ∀ y' : Out.baseOver (Spec (CommRingCat.of F)) ⟶ P'.A, y' ^ n = 1 →
      Out.WeilIs P'.A P'.L n u' y' 1 := by
    intro y' hy'
    have hy : push y' ^ n = 1 := by
      apply hi
      rw [MonObj.comp_pow, ← tbpush, ← tbpow, hy', tb1, MonObj.comp_one]
    exact pairing_weilMove hW inferInstance B.isLB P' hp w hw (tS := 𝟙 _) (t₀ := t) (Category.id_comp t).symm n
      u' y' hu' hy' u (push y') hu'g.symm rfl 1 (h _ hy)
  have h1 := hND F P' n hn u' hu' hall
  apply hi
  rw [← hpu, ← tbpush, h1, tb1, MonObj.comp_one]

section Act

variable {S : Scheme.{0}} {B : Out.PolAV S} {O : Type} [Ring O] [StarRing O] (o : B.OAct O) {T : Over S}

end Act

theorem pairing_tors {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [GrpObj G'] {T : Over S} (z : T ⟶ G)
    (f : G ⟶ G') (hf : IsMonHom f) (n : ℕ) (hz : z ^ n = 1) : (z ≫ f) ^ n = 1 := by
  have := hf
  rw [← MonObj.pow_comp, hz, MonObj.one_comp]

end
section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory



end
section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

end
section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj


end

section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

end

end GlobalTheory.LevelRigid
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearHomKillsTorsionOfWeilPairingDivisible

section

@[expose] public section

set_option autoImplicit false

open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section

namespace GlobalTheory.FlatCM.TorsKill

section Act

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {O : Type} [CommRing O] (o : OAct O G) {T : Over S}

theorem comp_act_zero (x : T ⟶ G) : x ≫ o.act 0 = 1 := by
  have h : x ≫ o.act (0 + 0) = (x ≫ o.act 0) * (x ≫ o.act 0) := by rw [o.add, MonObj.comp_mul]
  rw [add_zero] at h
  exact mul_left_cancel (a := x ≫ o.act 0) (by rw [_root_.mul_one]; exact h.symm)

theorem comp_act_nat (x : T ⟶ G) (n : ℕ) : x ≫ o.act (n : O) = x ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, pow_zero, comp_act_zero]
  | succ n ih => rw [Nat.cast_succ, o.add, MonObj.comp_mul, ih, o.one, Category.comp_id, pow_succ]

theorem comp_act_nat_mul (x : T ⟶ G) (n : ℕ) (hx : x ^ n = 1) (r : O) : x ≫ o.act ((n : O) * r) = 1 := by
  have := o.hom r
  rw [o.mul, ← Category.assoc, comp_act_nat, hx, MonObj.one_comp]

end Act

theorem weilIs_one_left (hW : Out.WeilSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) {T : Over S}
    (k : ℕ) (y : T ⟶ P.A) (hy : y ^ k = 1) : Out.WeilIs P.A P.L k 1 y 1 := by
  obtain ⟨e, he, hu⟩ := (hW S P k T).1 1 y (one_pow k) hy
  have h2 := (hW S P k T).2.1 1 1 y e e he he
  rw [_root_.one_mul] at h2
  have h3 : e * e = e := hu _ h2
  have he1 : e = 1 := mul_left_cancel (a := e) (by rw [_root_.mul_one]; exact h3)
  rwa [he1] at he

theorem kill : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (ψ : (X.A true).t.G ⟶ X.B.t.G),
    GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act ψ → ∀ n : ℕ, 0 < n →
    (∀ f : (X.A true).t.G ⟶ X.B.t.G, GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act f →
      (∃ m : ℕ, 0 < m ∧ ∃ z : Fin p → 𝓞 E, f ^ m = ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a)) →
      ∃ r : 𝓞 E, GlobalTheory.CM.WeilEq X.B.t.PP.L f ψ (X.A true).t.PP.L ((X.A true).t.act.act ((n : 𝓞 E) * r)) (𝟙 _)
        (spMap (σ₁.comp (algebraMap (𝓞 K) K)))) →
    ∀ u : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (X.A true).t.G, u ^ n = 1 → u ≫ ψ = 1 := by
  intro E _ _ _ H hH K _ _ ρ σ₁ p X ψ hψ n hn hWe u hu
  have laws := GlobalTheory.lawsFieldsSeparately
  have hWS : Out.WeilSt := laws.2.2.2.2.2.2.2.2.2.1
  have hND : Out.WeilNondegSt := laws.2.2.2.2.2.2.2.2.2.2.1
  have hBC : Out.PolBaseChangeSt := laws.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have u1 : unitOn (1 : ℂˣ) = 1 := map_one _

  have hgen : ∀ (x : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (X.A true).t.G)
      (f : (X.A true).t.G ⟶ X.B.t.G), x ^ n = 1 → Serre.IsLinearHom (X.A true).t.act X.B.t.act f →
      (∃ m : ℕ, 0 < m ∧ ∃ z : Fin p → 𝓞 E, f ^ m = ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a)) →
      Out.WeilIs X.B.pol.A X.B.pol.L n (x ≫ f) (u ≫ ψ) 1 := by
    intro x f hx hf hm
    obtain ⟨r, hr⟩ := hWe f hf hm
    have h := (hr n x u 1 hn hx hu).2
    rw [u1] at h
    apply h
    rw [comp_act_nat_mul _ x n hx r, Category.comp_id]
    exact weilIs_one_left hWS (X.A true).pol n u hu
  have hall : ∀ y : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G, y ^ n = 1 →
      Out.WeilIs X.B.pol.A X.B.pol.L n (u ≫ ψ) y 1 := by
    intro y hy
    have hψn : (u ≫ ψ) ^ n = 1 := GlobalTheory.LevelRigid.pairing_tors u ψ hψ.isMonHom n hu
    suffices h : Out.WeilIs X.B.pol.A X.B.pol.L n y (u ≫ ψ) 1 by
      have := GlobalTheory.CommPairing.weilIs_symm X.B.pol.isLB h
      rwa [inv_one] at this
    have hmem := GlobalTheory.T.torsion_cmUnitaryShimura_mem_closure_linearHom_images E H hH K ρ σ₁ p X n hn y hy
    clear hy
    induction hmem using Submonoid.closure_induction with
    | mem w hw =>
      obtain ⟨x, f, hx, hf, hm, rfl⟩ := hw
      exact hgen x f hx hf hm
    | one => exact weilIs_one_left hWS X.B.pol n (u ≫ ψ) hψn
    | mul a b _ _ ha hb =>
      have := (hWS _ X.B.pol n _).2.1 a b (u ≫ ψ) 1 1 ha hb
      rwa [_root_.mul_one] at this
  exact GlobalTheory.LevelRigid.pairing_nondeg hWS hND hBC X.B.pol ℂ _ n (Nat.cast_ne_zero.2 hn.ne') (u ≫ ψ)
    (GlobalTheory.LevelRigid.pairing_tors u ψ hψ.isMonHom n hu) hall

end GlobalTheory.FlatCM.TorsKill
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearHomKillsTorsionOfWeilPairingDivisibleStatement

section

@[expose] public section

open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

theorem _root_.GlobalTheory.T.linearHom_kills_torsion_of_weilPairing_divisible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (ψ : (X.A true).t.G ⟶ X.B.t.G),
    GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act ψ → ∀ n : ℕ, 0 < n →
    (∀ f : (X.A true).t.G ⟶ X.B.t.G, GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act f →
      (∃ m : ℕ, 0 < m ∧ ∃ z : Fin p → 𝓞 E, f ^ m = ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a)) →
      ∃ r : 𝓞 E, GlobalTheory.CM.WeilEq X.B.t.PP.L f ψ (X.A true).t.PP.L ((X.A true).t.act.act ((n : 𝓞 E) * r)) (𝟙 _)
        (spMap (σ₁.comp (algebraMap (𝓞 K) K)))) →
    ∀ u : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (X.A true).t.G, u ^ n = 1 → u ≫ ψ = 1 := by
  first | exact @GlobalTheory.FlatCM.TorsKill.kill | exact GlobalTheory.FlatCM.TorsKill.kill | (intros; apply GlobalTheory.FlatCM.TorsKill.kill <;> assumption)
end
end
