module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FibInit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Mon
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
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.CechAugRow
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TerminalRes
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FResLe
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FibInit
import Mathlib.Tactic.Linter.Style

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.CmAugCocycle

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

section Cm

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {E : Type u''} [Category.{v''} E]
  (j : C' ⥤ C) (ι : E ⥤ C) (e : E)

def cmL : StructuredArrow (ι.obj e) j ⥤ StructuredArrow e (Comma.fst ι j) where
  obj y := StructuredArrow.mk (Y := (⟨e, y.right, y.hom⟩ : Comma ι j)) (𝟙 e)
  map {y y'} f := StructuredArrow.homMk ⟨𝟙 e, f.right, by simp [StructuredArrow.w f]⟩ (by simp)
  map_id y := by ext <;> simp
  map_comp f g := by ext <;> simp

def cmU : StructuredArrow e (Comma.fst ι j) ⥤ StructuredArrow (ι.obj e) j where
  obj x := StructuredArrow.mk (Y := x.right.right) (ι.map x.hom ≫ x.right.hom)
  map {x x'} f := StructuredArrow.homMk f.right.right (by
    have h2 := StructuredArrow.w f
    dsimp at h2 ⊢
    rw [Category.assoc, ← f.right.w, ← Category.assoc, ← ι.map_comp, show x.hom ≫ f.right.left = x'.hom from h2])
  map_id x := by ext; simp
  map_comp f g := by ext; simp

theorem cm_w {y : StructuredArrow (ι.obj e) j} {x : StructuredArrow e (Comma.fst ι j)} (g : (cmL j ι e).obj y ⟶ x) :
    g.right.left = x.hom := by
  have h2 := StructuredArrow.w g
  dsimp [cmL] at h2
  simpa using h2

def cmAdj : cmL j ι e ⊣ cmU j ι e :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun y x =>
        { toFun := fun g => StructuredArrow.homMk g.right.right (by
            dsimp [cmL, cmU]
            rw [← cm_w j ι e g]
            exact g.right.w.symm)
          invFun := fun f => StructuredArrow.homMk
            { left := x.hom, right := f.right, w := (StructuredArrow.w f).symm } (by dsimp [cmL]; simp)
          left_inv := fun g => by
            apply StructuredArrow.ext
            apply Comma.hom_ext
            · exact (cm_w j ι e g).symm
            · rfl
          right_inv := fun f => by
            apply StructuredArrow.ext
            rfl }
      homEquiv_naturality_left_symm := by
        intro y' y x f g
        apply StructuredArrow.ext
        apply Comma.hom_ext
        all_goals (dsimp [cmL]; try simp)
      homEquiv_naturality_right := by
        intro y x x' f g
        apply StructuredArrow.ext
        dsimp [cmU]
        try simp }

end Cm

def cmMor {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {E : Type u''}
    [Category.{v''} E] (F : C ⥤ ModuleCat.{w} R) (j : C' ⥤ C) (ι : E ⥤ C) (e : E) :
    Mor (StructuredArrow.proj e (Comma.fst ι j) ⋙ Comma.snd ι j ⋙ j ⋙ F)
      (StructuredArrow.proj (ι.obj e) j ⋙ j ⋙ F) (RingHom.id R) where
  G := cmL j ι e
  τ _ := LinearMap.id
  nat _ _ := rfl

theorem cm_aug_cocycle {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R} (m : Mor F F' (RingHom.id R)) (T : C) (a : F.obj T) :
    d (StructuredArrow.proj T m.G ⋙ F') 0
      (aug (StructuredArrow.proj T m.G ⋙ F') (fun x => (m.τ x.right) ∘ₗ (F.map x.hom).hom) a) = 0 := by
  rw [← fib_aug m T]
  have := (relMor (𝟭 C) m T).hom.comm 0
    (aug (relF (𝟭 C) F T) (fun T' => ((relF (𝟭 C) F T).map ((fib_init T).to T')).hom) a)
  have h0 := (CrystallineSemistableComparison.P.initial (relF (𝟭 C) F T) _ (fib_init T)).1 a
  exact this.trans ((congrArg _ h0).trans (map_zero _))

theorem cm_transfer {R : Type} [CommRing R] {K : Cx.{w} R} {L : Cx.{w'} R} (φ : Cx.Hom K L (RingHom.id R))
    (hb : ∀ n, Function.Bijective (φ.mapH n)) {M : Type u''} [AddCommGroup M] [Module R M] (ε : M →ₗ[R] K.X 0)
    (hd : ∀ x, K.d 0 (ε x) = 0) (s : R) (hL : L.ResUpTo s (φ.f 0 ∘ₗ ε)) : K.ResUpTo s ε := by
  have h1 : ∀ n, UpTo (1 : R) (φ.mapH n) := fun n =>
    ((CrystallineSemistableComparison.P.upTo_alg (φ.mapH n) LinearMap.id (1 : R) 1).2.2.2.2).2 (hb n)
  have := (CrystallineSemistableComparison.P.res_transfer φ ε s 1 h1).2 hd hL
  rwa [mul_one] at this

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.comma1 : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {E : Type u''} [Category.{v''} E] (F : C ⥤ ModuleCat.{w} R) (j : C' ⥤ C) (ι : E ⥤ C) (s : R) (h : ∀ {x y : Comma ι j} (φ : x ⟶ y) (a : F.obj (ι.obj x.left)), (F.map y.hom).hom ((F.map (ι.map φ.left)).hom a) = (F.map (j.map φ.right)).hom ((F.map x.hom).hom a)), Desc s F j → ∀ n, IsoLe (s ^ (2 * n + 3)) n (⟨Comma.fst ι j, fun x => (F.map x.hom).hom, fun φ a => h φ a⟩ : Mor (ι ⋙ F) (Comma.snd ι j ⋙ j ⋙ F) (RingHom.id R)) := by
  intro R _ C _ C' _ E _ F j ι s h hD n
  refine CrystallineSemistableComparison.B.P.fib _ s (fun e => ?_) n
  have : (CrystallineSemistableComparison.B.cmMor F j ι e).G.IsLeftAdjoint := (CrystallineSemistableComparison.B.cmAdj j ι e).isLeftAdjoint
  refine CrystallineSemistableComparison.B.cm_transfer (CrystallineSemistableComparison.B.cmMor F j ι e).hom
    (fun k => CrystallineSemistableComparison.P.adj_mor (CrystallineSemistableComparison.B.cmMor F j ι e) (fun _ => Function.bijective_id) k) _
    (CrystallineSemistableComparison.B.cm_aug_cocycle (⟨Comma.fst ι j, fun x => (F.map x.hom).hom, fun φ a => h φ a⟩ : Mor (ι ⋙ F) (Comma.snd ι j ⋙ j ⋙ F) (RingHom.id R)) e) s ?_
  have eq : (CrystallineSemistableComparison.B.cmMor F j ι e).hom.f 0 ∘ₗ
      (aug (StructuredArrow.proj e (Comma.fst ι j) ⋙ Comma.snd ι j ⋙ j ⋙ F)
        fun x => (F.map x.right.hom).hom ∘ₗ ((ι ⋙ F).map x.hom).hom) = unAug F j (ι.obj e) := by
    apply LinearMap.ext; intro a; funext c
    change (F.map (c.obj (Fin.last 0)).hom).hom ((F.map (ι.map (𝟙 e))).hom a) = (F.map (c.obj (Fin.last 0)).hom).hom a
    rw [ι.map_id, F.map_id]
    rfl
  exact eq ▸ hD (ι.obj e)
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FFible

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

theorem fible_succ {R : Type} [CommRing R] {K : Cx.{w} R} {L : Cx.{w'} R} (φ : Cx.Hom K L (RingHom.id R)) (q : ℕ)
    (s₁ s₂ : R) (hK : ExactUpTo s₁ (K.d q) (K.d (q + 1))) (hφ : SurjUpTo s₂ (φ.mapH (q + 1))) :
    ExactUpTo (s₁ * s₂) (L.d q) (L.d (q + 1)) := by
  intro y hy
  obtain ⟨x, hx⟩ := hφ (L.cls y hy)
  obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K (q + 1)).1 x
  obtain ⟨c, hc⟩ := hK b hb
  have hfb : L.d (q + 1) (φ.f (q + 1) b) = 0 := by rw [φ.comm, hb, map_zero]
  have hy2 : L.d (q + 1) (s₂ • y) = 0 := by rw [map_smul, hy, smul_zero]
  have hy12 : L.d (q + 1) (s₁ • s₂ • y) = 0 := by rw [map_smul, hy2, smul_zero]
  have hs1b : L.d (q + 1) (s₁ • φ.f (q + 1) b) = 0 := by rw [map_smul, hfb, smul_zero]
  rw [CrystallineSemistableComparison.P.mapH_cls φ (q + 1) b hb hfb, ← resLe_cls_smul L (q + 1) s₂ y hy hy2] at hx
  have e1 : L.cls (s₁ • s₂ • y) hy12 = L.cls (s₁ • φ.f (q + 1) b) hs1b := by
    rw [resLe_cls_smul L (q + 1) s₁ _ hfb hs1b, hx, ← resLe_cls_smul L (q + 1) s₁ _ hy2 hy12]
  have e2 : L.cls (s₁ • φ.f (q + 1) b) hs1b = 0 := by
    refine resLe_cls_zero L (q + 1) _ hs1b ⟨φ.f q c, ?_⟩
    rw [φ.comm, hc, map_smul]
  rw [e2] at e1
  obtain ⟨c', hc'⟩ := ((CrystallineSemistableComparison.P.cls_surj L (q + 1)).2.1 _ hy12).1 e1
  exact ⟨c', by rw [hc', mul_smul]⟩

theorem fible_zero {R : Type} [CommRing R] {K : Cx.{w} R} {L : Cx.{w'} R} (φ : Cx.Hom K L (RingHom.id R))
    {A : Type u''} [AddCommGroup A] [Module R A] (ε : A →ₗ[R] K.X 0) (hd : ∀ x, K.d 0 (ε x) = 0) (s₁ s₂ : R)
    (hi : InjUpTo s₁ ε) (he : ExactUpTo s₁ ε (K.d 0)) (hφ : UpTo s₂ (φ.mapH 0)) :
    InjUpTo (s₁ * s₂) (φ.f 0 ∘ₗ ε) ∧ ExactUpTo (s₁ * s₂) (φ.f 0 ∘ₗ ε) (L.d 0) := by
  have hLd : ∀ x, L.d 0 (φ.f 0 (ε x)) = 0 := fun x => by rw [φ.comm, hd, map_zero]
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · have h1 : φ.mapH 0 (K.cls (ε x) (hd x)) = 0 := by
      rw [CrystallineSemistableComparison.P.mapH_cls φ 0 _ _ (hLd x)]
      exact resLe_cls_zero L 0 _ _ (by rw [show φ.f 0 (ε x) = 0 from hx]; exact Submodule.zero_mem _)
    have h2 := hφ.1 _ h1
    have hs' : K.d 0 (s₂ • ε x) = 0 := by rw [map_smul, hd, smul_zero]
    rw [← resLe_cls_smul K 0 s₂ _ _ hs'] at h2
    have h3 : s₂ • ε x = 0 := eq_zero_of_mem_boundaries_zero _ _ (((CrystallineSemistableComparison.P.cls_surj K 0).2.1 _ hs').1 h2)
    rw [← map_smul] at h3
    rw [mul_smul]
    exact hi _ h3
  · obtain ⟨x, hx⟩ := hφ.2 (L.cls y hy)
    obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K 0).1 x
    obtain ⟨a, ha⟩ := he b hb
    refine ⟨a, ?_⟩
    have hy' : L.d 0 (s₂ • y) = 0 := by rw [map_smul, hy, smul_zero]
    have hfb : L.d 0 (φ.f 0 b) = 0 := by rw [φ.comm, hb, map_zero]
    rw [CrystallineSemistableComparison.P.mapH_cls φ 0 b hb hfb, ← resLe_cls_smul L 0 s₂ y hy hy'] at hx
    have := ((CrystallineSemistableComparison.P.cls_surj L 0).2.2.1 _ _ hfb hy').1 hx
    have h4 : φ.f 0 b = s₂ • y := sub_eq_zero.1 (eq_zero_of_mem_boundaries_zero _ _ this)
    change φ.f 0 (ε a) = _
    rw [ha, map_smul, h4, mul_smul]

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.fible : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R} (m : Mor F F' (RingHom.id R)) (s : R) (n : ℕ), (∀ T : C, ∃ (E : Type v'') (_ : Category.{u''} E) (M : E ⥤ ModuleCat.{w} R) (μ : Mor M (StructuredArrow.proj T m.G ⋙ F') (RingHom.id R)) (e : ∀ x : E, F.obj T →ₗ[R] M.obj x) (s₁ s₂ : R), s = s₁ * s₂ ∧ (∀ x a, μ.τ x (e _ a) = m.τ x.right ((F.map x.hom).hom a)) ∧ (∀ (x y : E) (φ : x ⟶ y) a, (M.map φ).hom (e x a) = e y a) ∧ IsoLe s₂ (n + 1) μ ∧ InjUpTo s₁ (aug M e) ∧ ExactUpTo s₁ (aug M e) (d M 0) ∧ ∀ j ≤ n, ExactUpTo s₁ (d M j) (d M (j + 1))) → IsoLe (s ^ (2 * n + 3)) n m := by
  intro R _ C _ C' _ F F' m s n hT
  have key : ∀ (T : C), ∀ q ≤ n + 1, UpTo s ((relMor (𝟭 C) m T).pull q) := by
    intro T q hq
    obtain ⟨E, _, M, μ, e, s₁, s₂, rfl, hμe, he, hiso, hinj, hex0, hex⟩ := hT T
    have hK := CrystallineSemistableComparison.P.initial (relF (𝟭 C) F T) _ (fib_init T)
    cases q with
    | zero =>
      refine (resLe_zero (relMor (𝟭 C) m T).hom _ hK _).2 ?_
      have hd : ∀ a, d M 0 (aug M e a) = 0 := by
        intro a; funext c
        change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (M.map (GlobalTheory.CatH.toLast i c)).hom (e _ a) = 0
        simp only [he, Fin.sum_univ_two]
        simp
      have eqε : (relMor (𝟭 C) m T).hom.f 0 ∘ₗ
          aug (relF (𝟭 C) F T) (fun x => ((relF (𝟭 C) F T).map ((fib_init T).to x)).hom) =
          μ.hom.f 0 ∘ₗ aug M e := by
        have e1 : (relMor (𝟭 C) m T).hom.f 0 ∘ₗ
            aug (relF (𝟭 C) F T) (fun x => ((relF (𝟭 C) F T).map ((fib_init T).to x)).hom) =
            aug (relF (m.G ⋙ 𝟭 C) F' T) fun x => ((relMor (𝟭 C) m T).τ x) ∘ₗ
              ((relF (𝟭 C) F T).map ((fib_init T).to ((relMor (𝟭 C) m T).G.obj x))).hom :=
          LinearMap.ext fun a => funext fun c => rfl
        rw [e1, fib_aug]
        apply LinearMap.ext; intro a; funext c
        exact (hμe _ a).symm
      rw [eqε]
      exact fible_zero μ.hom (aug M e) hd s₁ s₂ hinj hex0 (hiso 0 (Nat.zero_le _))
    | succ q =>
      refine (resLe_succ (relMor (𝟭 C) m T).hom q (hK.2.2.2 q) _).2 ?_
      exact fible_succ μ.hom q s₁ s₂ (hex q (by omega)) (hiso (q + 1) (by omega)).2
  intro j hj
  have h1 := CrystallineSemistableComparison.P.rel (𝟭 C) m s j (fun i q hq => key i q (by omega))
  obtain ⟨k, rfl⟩ : ∃ k, n = j + k := ⟨n - j, by omega⟩
  have e : s ^ (2 * (j + k) + 3) = s ^ (2 * j + 3) * s ^ (2 * k) := by rw [← pow_add]; ring_nf
  rw [e]
  exact (CrystallineSemistableComparison.P.upTo_alg (m.pull j) LinearMap.id _ _).2.2.2.1 h1
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.GamDat

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

section gam

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']

theorem gam_h {E : Type u''} [Category.{v''} E] (F : C ⥤ ModuleCat.{w} R) (j : C' ⥤ C) (ι : E ⥤ C)
    {x y : Comma ι j} (φ : x ⟶ y) (a : F.obj (ι.obj x.left)) :
    (F.map y.hom).hom ((F.map (ι.map φ.left)).hom a) = (F.map (j.map φ.right)).hom ((F.map x.hom).hom a) := by
  rw [← ModuleCat.comp_apply, ← F.map_comp, ← ModuleCat.comp_apply, ← F.map_comp, φ.w]

def gamCm {E : Type u''} [Category.{v''} E] (F : C ⥤ ModuleCat.{w} R) (j : C' ⥤ C) (ι : E ⥤ C) :
    Mor (ι ⋙ F) (Comma.snd ι j ⋙ j ⋙ F) (RingHom.id R) :=
  ⟨Comma.fst ι j, fun x => (F.map x.hom).hom, fun φ a => gam_h F j ι φ a⟩

structure GamDat {Γ : Type} [CommMonoid Γ] {D : C} (γ : Γ →* End D) (j : C' ⥤ C) (t : C') where
  S : C
  il : D ⟶ S
  ir : j.obj t ⟶ S
  g : Γ →* End S
  hil : ∀ a, il ≫ (g a).asHom = (γ a).asHom ≫ il
  hir : ∀ a, ir ≫ (g a).asHom = ir
  hu : ∀ (t' : C') (c : D ⟶ j.obj t') (φ : j.obj t ⟶ j.obj t'), ∃! ψ : S ⟶ j.obj t', il ≫ ψ = c ∧ ir ≫ ψ = φ

namespace GamDat

variable {Γ : Type} [CommMonoid Γ] {D : C} {γ : Γ →* End D} {j : C' ⥤ C} {t : C'} (P : GamDat γ j t)

theorem uniq {t' : C'} (ψ ψ' : P.S ⟶ j.obj t') (h1 : P.il ≫ ψ = P.il ≫ ψ') (h2 : P.ir ≫ ψ = P.ir ≫ ψ') : ψ = ψ' :=
  (P.hu t' _ _).unique ⟨h1, h2⟩ ⟨rfl, rfl⟩

noncomputable def ψ (x : StructuredArrow t (Comma.snd (SingleObj.functor γ) j)) : P.S ⟶ j.obj x.right.right :=
  (P.hu x.right.right x.right.hom (j.map x.hom)).exists.choose

theorem ψ_spec (x : StructuredArrow t (Comma.snd (SingleObj.functor γ) j)) :
    P.il ≫ P.ψ x = x.right.hom ∧ P.ir ≫ P.ψ x = j.map x.hom :=
  (P.hu x.right.right x.right.hom (j.map x.hom)).exists.choose_spec

theorem ψ_nat {x y : StructuredArrow t (Comma.snd (SingleObj.functor γ) j)} (f : x ⟶ y) :
    (P.g f.right.left).asHom ≫ P.ψ y = P.ψ x ≫ j.map f.right.right := by
  have hw : (γ f.right.left).asHom ≫ y.right.hom = x.right.hom ≫ j.map f.right.right := f.right.w
  have hw' : x.hom ≫ f.right.right = y.hom := StructuredArrow.w f
  apply P.uniq
  · rw [← Category.assoc, P.hil, Category.assoc, (P.ψ_spec y).1, ← Category.assoc, (P.ψ_spec x).1, hw]
  · rw [← Category.assoc, P.hir, (P.ψ_spec y).2, ← Category.assoc, (P.ψ_spec x).2, ← j.map_comp, hw']

noncomputable def μ (F : C ⥤ ModuleCat.{w} R) : Mor (SingleObj.functor P.g ⋙ F)
    (StructuredArrow.proj t (Comma.snd (SingleObj.functor γ) j) ⋙ (Comma.snd (SingleObj.functor γ) j ⋙ j ⋙ F))
    (RingHom.id R) where
  G := StructuredArrow.proj t (Comma.snd (SingleObj.functor γ) j) ⋙ Comma.fst (SingleObj.functor γ) j
  τ x := (F.map (P.ψ x)).hom
  nat {x y} f a := by
    show (F.map (P.ψ y)).hom ((F.map (P.g f.right.left).asHom).hom a) =
      (F.map (j.map f.right.right)).hom ((F.map (P.ψ x)).hom a)
    rw [← ModuleCat.comp_apply, ← F.map_comp, ← ModuleCat.comp_apply, ← F.map_comp, P.ψ_nat]

noncomputable def Ψ [j.Full] [j.Faithful] :
    Comma (SingleObj.functor P.g) j ⥤ StructuredArrow t (Comma.snd (SingleObj.functor γ) j) where
  obj X := StructuredArrow.mk (Y := ({ left := X.left, right := X.right, hom := P.il ≫ X.hom } :
      Comma (SingleObj.functor γ) j)) (j.preimage (P.ir ≫ X.hom))
  map {X Y} f := StructuredArrow.homMk
    { left := f.left, right := f.right
      w := by
        have hw : (P.g f.left).asHom ≫ Y.hom = X.hom ≫ j.map f.right := f.w
        show (γ f.left).asHom ≫ P.il ≫ Y.hom = (P.il ≫ X.hom) ≫ j.map f.right
        rw [← Category.assoc, ← P.hil, Category.assoc, hw, Category.assoc] }
    (by
      have hw : (P.g f.left).asHom ≫ Y.hom = X.hom ≫ j.map f.right := f.w
      apply j.map_injective
      show j.map (j.preimage (P.ir ≫ X.hom) ≫ f.right) = j.map (j.preimage (P.ir ≫ Y.hom))
      rw [j.map_comp, Functor.map_preimage, Functor.map_preimage, Category.assoc, ← hw, ← Category.assoc, P.hir])
  map_id X := StructuredArrow.hom_ext _ _ (CommaMorphism.ext rfl rfl)
  map_comp f g := StructuredArrow.hom_ext _ _ (CommaMorphism.ext rfl rfl)

theorem ψΨ [j.Full] [j.Faithful] (T : Comma (SingleObj.functor P.g) j) : P.ψ (P.Ψ.obj T) = T.hom := by
  apply P.uniq
  · rw [(P.ψ_spec _).1]; rfl
  · rw [(P.ψ_spec _).2]; exact j.map_preimage _

theorem Ψ_full [j.Full] [j.Faithful] : P.Ψ.Full where
  map_surjective {X Y} f := by
    have w1 : (γ f.right.left).asHom ≫ (P.il ≫ Y.hom) = (P.il ≫ X.hom) ≫ j.map f.right.right := f.right.w
    have w2 : j.preimage (P.ir ≫ X.hom) ≫ f.right.right = j.preimage (P.ir ≫ Y.hom) := StructuredArrow.w f
    have w : (P.g f.right.left).asHom ≫ Y.hom = X.hom ≫ j.map f.right.right := by
      apply P.uniq
      · rw [← Category.assoc, P.hil, Category.assoc, w1, Category.assoc]
      · rw [← Category.assoc, P.hir, ← Category.assoc, ← j.map_preimage (P.ir ≫ X.hom), ← j.map_comp, w2,
          j.map_preimage]
    exact ⟨{ left := f.right.left, right := f.right.right, w := w }, StructuredArrow.hom_ext _ _ (CommaMorphism.ext rfl rfl)⟩

theorem Ψ_faithful [j.Full] [j.Faithful] : P.Ψ.Faithful where
  map_injective {_ _} {_ _} h := CommaMorphism.ext (congrArg (fun f => f.right.left) h) (congrArg (fun f => f.right.right) h)

theorem Ψ_essSurj [j.Full] [j.Faithful] : P.Ψ.EssSurj where
  mem_essImage Y := by
    let X : Comma (SingleObj.functor P.g) j := { left := Y.right.left, right := Y.right.right, hom := P.ψ Y }
    refine ⟨X, ⟨StructuredArrow.isoMk (Comma.isoMk (Iso.refl _) (Iso.refl _) ?_) ?_⟩⟩
    · show (SingleObj.functor γ).map (𝟙 Y.right.left) ≫ Y.right.hom = (P.il ≫ P.ψ Y) ≫ j.map (𝟙 _)
      erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
      exact (P.ψ_spec Y).1.symm
    · show j.preimage (P.ir ≫ P.ψ Y) ≫ 𝟙 _ = Y.hom
      rw [Category.comp_id, (P.ψ_spec Y).2, j.preimage_map]

theorem Ψ_equiv [j.Full] [j.Faithful] : P.Ψ.IsEquivalence := by
  have := P.Ψ_full
  have := P.Ψ_faithful
  have := P.Ψ_essSurj
  exact {}

theorem μ_iso [j.Full] [j.Faithful] (F : C ⥤ ModuleCat.{w} R) (s : R) (hD : Desc s F j) (n : ℕ) :
    IsoLe (1 * s ^ (2 * (n + 1) + 3)) (n + 1) (P.μ F) := by
  intro q hq
  have h1 : UpTo (s ^ (2 * (n + 1) + 3)) ((gamCm F j (SingleObj.functor P.g)).pull q) :=
    CrystallineSemistableComparison.B.P.comma1 F j (SingleObj.functor P.g) s (fun φ a => gam_h F j _ φ a) hD (n + 1) q hq
  have := P.Ψ_equiv
  let F' := StructuredArrow.proj t (Comma.snd (SingleObj.functor γ) j) ⋙ (Comma.snd (SingleObj.functor γ) j ⋙ j ⋙ F)
  have hb : UpTo (1 : R) ((Mor.restrict F' P.Ψ).pull q) :=
    ((CrystallineSemistableComparison.P.upTo_alg ((Mor.restrict F' P.Ψ).pull q) LinearMap.id (1 : R) 1).2.2.2.2).2
      (CrystallineSemistableComparison.P.adj F' P.Ψ _ P.Ψ.asEquivalence.toAdjunction q)
  let η : Comma.fst (SingleObj.functor P.g) j ⟶
      P.Ψ ⋙ (StructuredArrow.proj t (Comma.snd (SingleObj.functor γ) j) ⋙ Comma.fst (SingleObj.functor γ) j) :=
    { app := fun X => 𝟙 X.left
      naturality := fun X Y f => by
        show f.left ≫ 𝟙 Y.left = 𝟙 X.left ≫ f.left
        rw [Category.comp_id, Category.id_comp] }
  have heq : (Mor.restrict F' P.Ψ).pull q ∘ₗ (P.μ F).pull q = (gamCm F j (SingleObj.functor P.g)).pull q := by
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, ← (CrystallineSemistableComparison.P.pull_comp (P.μ F) (Mor.restrict F' P.Ψ) q x).1]
    refine (CrystallineSemistableComparison.P.prism (gamCm F j (SingleObj.functor P.g)) ((P.μ F).comp (Mor.restrict F' P.Ψ)) η ?_ q x).symm
    intro T a
    show (F.map (P.ψ (P.Ψ.obj T))).hom ((F.map ((SingleObj.functor P.g).map (𝟙 T.left))).hom a) = (F.map T.hom).hom a
    rw [CategoryTheory.Functor.map_id, F.map_id, ModuleCat.id_apply, P.ψΨ]
    rfl
  rw [← heq] at h1
  exact (CrystallineSemistableComparison.P.upTo_alg ((P.μ F).pull q) ((Mor.restrict F' P.Ψ).pull q) (1 : R) _).2.2.1 hb h1

end GamDat

end gam

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.gam : ∀ n : ℕ, ∃ N : ℕ, ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] (F : C ⥤ ModuleCat.{w} R) (j : C' ⥤ C) [j.Full] [j.Faithful] (Γ : Type) [CommMonoid Γ] (D : C) (γ : Γ →* End D) (s : R), Desc s F j → (∀ t : C', ∃ (S : C) (il : D ⟶ S) (ir : j.obj t ⟶ S) (g : Γ →* End S), (∀ a, il ≫ (g a).asHom = (γ a).asHom ≫ il) ∧ (∀ a, ir ≫ (g a).asHom = ir) ∧ (∀ (t' : C') (c : D ⟶ j.obj t') (φ : j.obj t ⟶ j.obj t'), ∃! ψ : S ⟶ j.obj t', il ≫ ψ = c ∧ ir ≫ ψ = φ) ∧ InjUpTo s (aug (SingleObj.functor g ⋙ F) fun _ => (F.map ir).hom) ∧ ExactUpTo s (aug (SingleObj.functor g ⋙ F) fun _ => (F.map ir).hom) (d (SingleObj.functor g ⋙ F) 0) ∧ ∀ i ≤ n, ExactUpTo s (d (SingleObj.functor g ⋙ F) i) (d (SingleObj.functor g ⋙ F) (i + 1))) → RI (s ^ N) n F (SingleObj.functor γ) := by
  intro n
  refine ⟨(2 * n + 3) + ((2 * n + 3) + (2 * n + 6) * (2 * n + 3)), ?_⟩
  intro R _ C _ C' _ F j _ _ Γ _ D γ s hD hT q hq
  have hA : UpTo (s ^ (2 * n + 3)) ((gamCm F j (SingleObj.functor γ)).pull q) :=
    CrystallineSemistableComparison.B.P.comma1 F j (SingleObj.functor γ) s (fun φ a => gam_h F j _ φ a) hD n q hq
  have hC : UpTo (s ^ (2 * n + 3)) ((Mor.restrict F j).pull q) :=
    CrystallineSemistableComparison.B.P.fib (Mor.restrict F j) s (fun T => hD T) n q hq
  have hS : UpTo ((s * (1 * s ^ (2 * (n + 1) + 3))) ^ (2 * n + 3))
      ((Mor.restrict (j ⋙ F) (Comma.snd (SingleObj.functor γ) j)).pull q) := by
    refine CrystallineSemistableComparison.B.P.fible (Mor.restrict (j ⋙ F) (Comma.snd (SingleObj.functor γ) j)) (s * (1 * s ^ (2 * (n + 1) + 3))) n
      (fun t => ?_) q hq
    obtain ⟨S, il, ir, g, hil, hir, hu, hinj, hex0, hex⟩ := hT t
    let P : GamDat γ j t := ⟨S, il, ir, g, hil, hir, hu⟩
    refine ⟨SingleObj Γ, inferInstance, SingleObj.functor g ⋙ F, P.μ F, fun _ => (F.map ir).hom, s,
      1 * s ^ (2 * (n + 1) + 3), rfl, ?_, ?_, P.μ_iso F s hD n, hinj, hex0, hex⟩
    · intro x a
      show (F.map (P.ψ x)).hom ((F.map ir).hom a) = (F.map (j.map x.hom)).hom a
      rw [← ModuleCat.comp_apply, ← F.map_comp, (P.ψ_spec x).2]
      rfl
    · intro x y φ a
      show (F.map (g φ).asHom).hom ((F.map ir).hom a) = (F.map ir).hom a
      rw [← ModuleCat.comp_apply, ← F.map_comp, hir]
  have heq : (gamCm F j (SingleObj.functor γ)).pull q ∘ₗ (Mor.restrict F (SingleObj.functor γ)).pull q =
      (Mor.restrict (j ⋙ F) (Comma.snd (SingleObj.functor γ) j)).pull q ∘ₗ (Mor.restrict F j).pull q := by
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply,
      ← (CrystallineSemistableComparison.P.pull_comp (Mor.restrict F (SingleObj.functor γ)) (gamCm F j (SingleObj.functor γ)) q x).1,
      ← (CrystallineSemistableComparison.P.pull_comp (Mor.restrict F j) (Mor.restrict (j ⋙ F) (Comma.snd (SingleObj.functor γ) j)) q x).1]
    refine CrystallineSemistableComparison.P.prism _ _ (Comma.natTrans (SingleObj.functor γ) j) (fun T a => rfl) q x
  have h2 := (CrystallineSemistableComparison.P.upTo_alg _ _ _ _).1 hC hS
  rw [← heq] at h2
  have h3 := (CrystallineSemistableComparison.P.upTo_alg _ _ _ _).2.2.1 hA h2
  have e : s ^ ((2 * n + 3) + ((2 * n + 3) + (2 * n + 6) * (2 * n + 3))) =
      s ^ (2 * n + 3) * (s ^ (2 * n + 3) * (s * (1 * s ^ (2 * (n + 1) + 3))) ^ (2 * n + 3)) := by ring
  rw [e]
  exact h3
end
end
