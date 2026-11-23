module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsSpecProdBijectiveStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeHomSections
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackBiprodInlInrBijective
import Mathlib.Tactic.TypeStar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleChainsDiscBiprodDescIsIso

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.ChainsIso

variable (R : Type) [CommRing R]

theorem chains_map_f {E E' : Spc} (g : E ⟶ E') (p : ℕ) :
    ((chains R).map g).f (-(p : ℤ)) =
      (chainsXIso R E p).hom ≫ (free R).map (g.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E' p).inv := by
  have h1 : ((chains R).map g).f (-(p : ℤ)) =
      (chainsXIso R E p).hom ≫ (((chainsN R).map g).f p) ≫ (chainsXIso R E' p).inv :=
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat (i := p) rfl
  rw [h1]
  rfl

theorem chains_isZero (E : Spc) (i : ℤ) (hi : 0 < i) : IsZero (((chains R).obj E).X i) := by
  apply HomologicalComplex.isZero_extend_X
  intro n h
  change -(n : ℤ) = i at h
  omega

end ChainsIso


open ChainsIso in
theorem chains_disc_biprod_isIso : ∀ (R : Type) [CommRing R] {P₁ P₂ Q : PSh} (f₁ : P₁ ⟶ Q) (f₂ : P₂ ⟶ Q),
    IsIso (biprod.desc ((free R).map f₁) ((free R).map f₂)) →
      IsIso (biprod.desc ((chains R).map (disc.map f₁)) ((chains R).map (disc.map f₂))) := by
  intro R _ P₁ P₂ Q f₁ f₂ h
  suffices hc : ∀ i, IsIso ((biprod.desc ((chains R).map (disc.map f₁)) ((chains R).map (disc.map f₂))).f i) from
    HomologicalComplex.Hom.isIso_of_components _
  intro i
  have e := biprod.mapBiprod_hom_desc (HomologicalComplex.eval (Shv R) (ComplexShape.up ℤ) i)
    (f := (chains R).map (disc.map f₁)) (g := (chains R).map (disc.map f₂))
  change IsIso ((HomologicalComplex.eval (Shv R) (ComplexShape.up ℤ) i).map _)
  rw [← e]
  suffices hs : IsIso (biprod.desc (((chains R).map (disc.map f₁)).f i) (((chains R).map (disc.map f₂)).f i)) by
    exact IsIso.comp_isIso' inferInstance hs
  rcases lt_or_ge 0 i with hi | hi
  · have h1 := chains_isZero R (disc.obj P₁) i hi
    have h2 := chains_isZero R (disc.obj P₂) i hi
    have hQ := chains_isZero R (disc.obj Q) i hi
    refine ⟨⟨0, ?_, hQ.eq_of_src _ _⟩⟩
    apply biprod.hom_ext'
    · exact h1.eq_of_src _ _
    · exact h2.eq_of_src _ _
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨i.natAbs, by omega⟩
    rw [chains_map_f, chains_map_f]
    have hfree : IsIso (biprod.desc ((free R).map ((disc.map f₁).app (op (SimplexCategory.mk p))))
        ((free R).map ((disc.map f₂).app (op (SimplexCategory.mk p))))) := h
    have hc : biprod.desc ((chainsXIso R (disc.obj P₁) p).hom ≫ (free R).map ((disc.map f₁).app (op (SimplexCategory.mk p))) ≫
          (chainsXIso R (disc.obj Q) p).inv)
        ((chainsXIso R (disc.obj P₂) p).hom ≫ (free R).map ((disc.map f₂).app (op (SimplexCategory.mk p))) ≫
          (chainsXIso R (disc.obj Q) p).inv) =
        biprod.map (chainsXIso R (disc.obj P₁) p).hom (chainsXIso R (disc.obj P₂) p).hom ≫
          biprod.desc ((free R).map ((disc.map f₁).app (op (SimplexCategory.mk p))))
            ((free R).map ((disc.map f₂).app (op (SimplexCategory.mk p)))) ≫ (chainsXIso R (disc.obj Q) p).inv := by
      apply biprod.hom_ext' <;> simp
    rw [hc]
    exact IsIso.comp_isIso' (show IsIso (biprod.mapIso (chainsXIso R (disc.obj P₁) p) (chainsXIso R (disc.obj P₂) p)).hom
      from inferInstance) (IsIso.comp_isIso' hfree inferInstance)

end GlobalTheory.EtC
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleChainsDiscBiprodDescIsIsoStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleChains_disc_biprod_desc_isIso : ∀ (R : Type) [CommRing R] {P₁ P₂ Q : PSh} (f₁ : P₁ ⟶ Q) (f₂ : P₂ ⟶ Q), IsIso (biprod.desc ((free R).map f₁) ((free R).map f₂)) → IsIso (biprod.desc ((chains R).map (disc.map f₁)) ((chains R).map (disc.map f₂))) := by
  first | exact @GlobalTheory.EtC.chains_disc_biprod_isIso | exact GlobalTheory.EtC.chains_disc_biprod_isIso | (intros; apply GlobalTheory.EtC.chains_disc_biprod_isIso <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleSheafBiprodDescIsIsoOfResBijective

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

section FreeYoneda
variable {R : Type} [CommRing R]

theorem freeYoneda_secMap_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (s : Sec F U) :
    Sec.map φ (Sec.res g s) = Sec.res g (Sec.map φ s) := by
  have h := congrArg (fun k => k.hom s) (φ.hom.naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

theorem freeYoneda_res_res {F : Shv R} {W V U : Scheme.{0}} (g : W ⟶ V) (x : V ⟶ U) (s : Sec F U) :
    Sec.res g (Sec.res x s) = Sec.res (g ≫ x) s := by
  change (F.obj.map g.op).hom ((F.obj.map x.op).hom s) = (F.obj.map (g ≫ x).op).hom s
  rw [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem freeYoneda_res_id {F : Shv R} {U : Scheme.{0}} (s : Sec F U) : Sec.res (𝟙 U) s = s := by
  change (F.obj.map (𝟙 U).op).hom s = s
  rw [op_id, CategoryTheory.Functor.map_id, ModuleCat.hom_id, LinearMap.id_apply]

theorem freeYoneda_secMap_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (s : Sec F U) :
    Sec.map (φ ≫ ψ) s = Sec.map ψ (Sec.map φ s) := rfl


variable (R) in
theorem freeYoneda_gen {Y U : Scheme.{0}} (x : U ⟶ Y) :
    freeGen R (yoneda.obj Y) U x = Sec.res x (freeGen R (yoneda.obj Y) Y (𝟙 Y)) := by
  rw [(free_hom_sections R (yoneda.obj Y) ((free R).obj (yoneda.obj Y))).2.2.1]
  simp


variable (R) in
theorem freeYoneda_ev_bijective {Y : Scheme.{0}} (F : Shv R) :
    Function.Bijective fun h : (free R).obj (yoneda.obj Y) ⟶ F => Sec.map h (freeGen R (yoneda.obj Y) Y (𝟙 Y)) := by
  obtain ⟨hex, hext, -, -⟩ := free_hom_sections R (yoneda.obj Y) F
  constructor
  · intro φ ψ e
    apply hext
    intro U x
    rw [freeYoneda_gen R (x : U ⟶ Y), freeYoneda_secMap_res, freeYoneda_secMap_res]
    exact congrArg (Sec.res (x : U ⟶ Y)) e
  · intro s
    obtain ⟨φ, hφ⟩ := hex (fun U x => Sec.res (x : U ⟶ Y) s) (fun V U g x => by
      simp only [yoneda_obj_map]
      exact freeYoneda_res_res g x s)
    exact ⟨φ, (hφ Y (𝟙 Y)).trans (freeYoneda_res_id s)⟩


variable (R) in
theorem freeYoneda_ev_pre {Y X : Scheme.{0}} (f : Y ⟶ X) {F : Shv R} (h : (free R).obj (yoneda.obj X) ⟶ F) :
    Sec.map ((free R).map (yoneda.map f) ≫ h) (freeGen R (yoneda.obj Y) Y (𝟙 Y)) =
      Sec.res f (Sec.map h (freeGen R (yoneda.obj X) X (𝟙 X))) := by
  rw [freeYoneda_secMap_comp, (free_hom_sections R (yoneda.obj Y) F).2.2.2, ← freeYoneda_secMap_res,
    ← freeYoneda_gen R f]
  congr 2

end FreeYoneda

theorem freeYoneda_desc_isIso : ∀ (R : Type) [CommRing R] {Y₁ Y₂ X : Scheme.{0}} (f₁ : Y₁ ⟶ X) (f₂ : Y₂ ⟶ X),
    (∀ F : Shv R, Function.Bijective fun s : Sec F X => (Sec.res f₁ s, Sec.res f₂ s)) →
    IsIso (biprod.desc ((free R).map (yoneda.map f₁)) ((free R).map (yoneda.map f₂))) := by
  intro R _ Y₁ Y₂ X f₁ f₂ hb
  rw [isIso_iff_coyoneda_map_bijective]
  intro F
  have key : Function.Bijective fun h : (free R).obj (yoneda.obj X) ⟶ F =>
      ((free R).map (yoneda.map f₁) ≫ h, (free R).map (yoneda.map f₂) ≫ h) := by
    have e12 := (freeYoneda_ev_bijective R (Y := Y₁) F).prodMap (freeYoneda_ev_bijective R (Y := Y₂) F)
    refine (e12.of_comp_iff' _).1 ?_
    have comm : (Prod.map (fun h : (free R).obj (yoneda.obj Y₁) ⟶ F => Sec.map h (freeGen R (yoneda.obj Y₁) Y₁ (𝟙 Y₁)))
        (fun h : (free R).obj (yoneda.obj Y₂) ⟶ F => Sec.map h (freeGen R (yoneda.obj Y₂) Y₂ (𝟙 Y₂)))) ∘
        (fun h : (free R).obj (yoneda.obj X) ⟶ F =>
          ((free R).map (yoneda.map f₁) ≫ h, (free R).map (yoneda.map f₂) ≫ h)) =
        (fun s : Sec F X => (Sec.res f₁ s, Sec.res f₂ s)) ∘
          (fun h : (free R).obj (yoneda.obj X) ⟶ F => Sec.map h (freeGen R (yoneda.obj X) X (𝟙 X))) := by
      funext h
      simp only [Function.comp_apply, Prod.map_apply]
      rw [freeYoneda_ev_pre R f₁ h, freeYoneda_ev_pre R f₂ h]
    rw [comm]
    exact (hb F).comp (freeYoneda_ev_bijective R F)
  have hβ : Function.Bijective fun g : ((free R).obj (yoneda.obj Y₁) ⊞ (free R).obj (yoneda.obj Y₂)) ⟶ F =>
      (biprod.inl ≫ g, biprod.inr ≫ g) := by
    constructor
    · intro g g' e
      simp only [Prod.mk.injEq] at e
      exact biprod.hom_ext' _ _ e.1 e.2
    · rintro ⟨a, b⟩
      exact ⟨biprod.desc a b, by simp⟩
  refine (hβ.of_comp_iff' _).1 ?_
  convert key using 1
  funext h
  simp

end GlobalTheory.EtC
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleSheafBiprodDescIsIsoOfResBijectiveStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.freeEtaleSheaf_biprodDesc_isIso_of_res_bijective : ∀ (R : Type) [CommRing R] {Y₁ Y₂ X : Scheme.{0}} (f₁ : Y₁ ⟶ X) (f₂ : Y₂ ⟶ X), (∀ F : Shv R, Function.Bijective fun s : Sec F X => (Sec.res f₁ s, Sec.res f₂ s)) → IsIso (biprod.desc ((free R).map (yoneda.map f₁)) ((free R).map (yoneda.map f₂))) := by
  first | exact @GlobalTheory.EtC.freeYoneda_desc_isIso | exact GlobalTheory.EtC.freeYoneda_desc_isIso | (intros; apply GlobalTheory.EtC.freeYoneda_desc_isIso <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyProdRingProjectionsBijective

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.ProdCoh

theorem cpull_bijective_of_isIso {R : Type} [CommRing R] {K L : Cx R} (c : K ⟶ L) [IsIso c] (I : Cx R) (n : ℤ) :
    Function.Bijective (cpull c I n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨cpull (inv c) I n, fun x => ?_, fun x => ?_⟩
  · rw [BiprodCls.cpull_cpull, IsIso.inv_hom_id, BiprodCls.cpull_id]
  · rw [BiprodCls.cpull_cpull, IsIso.hom_inv_id, BiprodCls.cpull_id]

theorem bij_of_eq {α β : Sort*} {f g : α → β} (h : ∀ x, f x = g x) (hg : Function.Bijective g) :
    Function.Bijective f := by
  rw [show f = g from funext h]; exact hg

theorem ht_prod_bijective : ∀ (q : ℕ) (A B : Type) [CommRing A] [CommRing B] (n i : ℤ),
    Function.Bijective (fun x : Ht q (sp (A × B)) n i =>
      (pull _ (spMap (RingHom.fst A B)) _ _ x, pull _ (spMap (RingHom.snd A B)) _ _ x)) := by
  intro q A B _ _ n i
  have h2 := GlobalTheory.T.freeEtaleSheaf_biprodDesc_isIso_of_res_bijective (ZMod q) _ _ (GlobalTheory.T.etaleSheafSections_specProd_bijective (ZMod q) A B)
  have h3 := GlobalTheory.T.etaleChains_disc_biprod_desc_isIso (ZMod q) _ _ h2
  have hc := @cpull_bijective_of_isIso _ _ _ _ _ h3 (res (ZMod q) (tw q i)) n
  have := (cpull_biprod_bijective (ZMod q) _ _ (res (ZMod q) (tw q i)) n).comp hc
  refine bij_of_eq (fun x => ?_) this
  dsimp only [Function.comp]
  erw [BiprodCls.cpull_cpull, BiprodCls.cpull_cpull, biprod.inl_desc, biprod.inr_desc]
  rfl

end GlobalTheory.EtC.ProdCoh
end
end
