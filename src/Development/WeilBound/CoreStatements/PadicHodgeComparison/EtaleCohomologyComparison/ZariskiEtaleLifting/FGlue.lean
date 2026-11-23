module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Aesop.BuiltinRules
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.DcColSurj
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
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FRiCalc
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FTors
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FibInit
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Tactic.Lemma

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FNiCoh

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

section NiCoh

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C]

theorem ni_nat {F F' : C ⥤ ModuleCat.{w} R} (β : F ⟶ F') {T T' : C} (φ : T ⟶ T') (x : F.obj T) :
    (β.app T').hom ((F.map φ).hom x) = (F'.map φ).hom ((β.app T).hom x) := by
  rw [← ModuleCat.comp_apply, β.naturality, ModuleCat.comp_apply]

theorem ni_pull_cls {F F' : C ⥤ ModuleCat.{w} R} (β : F ⟶ F') (n : ℕ) (a : Cn F n) (ha : d F n a = 0) :
    ∃ hb, (Mor.ofNatTrans β).pull n ((cx F).cls a ha) = (cx F').cls (fun s => (β.app _).hom (a s)) hb := by
  have hb : d F' n (fun s => (β.app _).hom (a s)) = 0 :=
    ((Mor.ofNatTrans β).d_pullC n a).trans (by rw [ha, map_zero])
  exact ⟨hb, CrystallineSemistableComparison.P.mapH_cls (Mor.ofNatTrans β).hom n a ha hb⟩

theorem ni_pull_add {F F' : C ⥤ ModuleCat.{w} R} (β β' : F ⟶ F') (n : ℕ) (x : H F n) :
    (Mor.ofNatTrans (β + β')).pull n x = (Mor.ofNatTrans β).pull n x + (Mor.ofNatTrans β').pull n x := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F) n).1 x
  obtain ⟨h1, e1⟩ := ni_pull_cls (β + β') n a ha
  obtain ⟨h2, e2⟩ := ni_pull_cls β n a ha
  obtain ⟨h3, e3⟩ := ni_pull_cls β' n a ha
  rw [e1, e2, e3, ← (CrystallineSemistableComparison.P.cls_surj (cx F') n).2.2.2.1 _ _ h2 h3 (by rw [map_add (f := _), h2, h3, add_zero])]
  congr 1

theorem ni_pull_zero {F F' : C ⥤ ModuleCat.{w} R} (n : ℕ) (x : H F n) :
    (Mor.ofNatTrans (0 : F ⟶ F')).pull n x = 0 := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F) n).1 x
  obtain ⟨h1, e1⟩ := ni_pull_cls (0 : F ⟶ F') n a ha
  rw [e1, (CrystallineSemistableComparison.P.cls_surj (cx F') n).2.1]
  have : (fun s => ((0 : F ⟶ F').app _).hom (a s)) = (0 : Cn F' n) := by
    funext s
    simp only [NatTrans.app_zero, ModuleCat.hom_zero, LinearMap.zero_apply, Pi.zero_apply]
  rw [this]
  exact Submodule.zero_mem _

theorem ni_pull_sum {ι : Type} {F F' : C ⥤ ModuleCat.{w} R} (β : ι → (F ⟶ F')) (S : Finset ι) (n : ℕ) (x : H F n) :
    (Mor.ofNatTrans (∑ k ∈ S, β k)).pull n x = ∑ k ∈ S, (Mor.ofNatTrans (β k)).pull n x := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, ni_pull_zero]
  | insert k S hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, ni_pull_add, ih]

theorem ni_pull_comp {F F' F'' : C ⥤ ModuleCat.{w} R} (β : F ⟶ F') (β' : F' ⟶ F'') (n : ℕ) (x : H F n) :
    (Mor.ofNatTrans (β ≫ β')).pull n x = (Mor.ofNatTrans β').pull n ((Mor.ofNatTrans β).pull n x) := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F) n).1 x
  obtain ⟨h1, e1⟩ := ni_pull_cls (β ≫ β') n a ha
  obtain ⟨h2, e2⟩ := ni_pull_cls β n a ha
  obtain ⟨h3, e3⟩ := ni_pull_cls β' n _ h2
  rw [e1, e2, e3]
  rfl

theorem ni_pull_id {F : C ⥤ ModuleCat.{w} R} (n : ℕ) (x : H F n) :
    (Mor.ofNatTrans (𝟙 F)).pull n x = x := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F) n).1 x
  obtain ⟨h1, e1⟩ := ni_pull_cls (𝟙 F) n a ha
  rw [e1]
  rfl

def fixF {F : C ⥤ ModuleCat.{w} R} (e : F ⟶ F) : SubF F where
  S T := LinearMap.ker ((e.app T).hom - LinearMap.id)
  map_mem := fun {_ _} φ {_} hx => by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hx ⊢
    rw [ni_nat, hx]

theorem mem_fixF {F : C ⥤ ModuleCat.{w} R} (e : F ⟶ F) (T : C) (x : F.obj T) :
    x ∈ (fixF e).S T ↔ (e.app T).hom x = x := by
  change x ∈ LinearMap.ker ((e.app T).hom - LinearMap.id) ↔ _
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

def fixP {F : C ⥤ ModuleCat.{w} R} (e : F ⟶ F) (he : e ≫ e = e) : F ⟶ (fixF e).fn where
  app T := ModuleCat.ofHom (LinearMap.codRestrict _ (e.app T).hom fun x => by
    rw [mem_fixF, ← ModuleCat.comp_apply, ← NatTrans.comp_app, he])
  naturality T T' φ := ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext (ni_nat e φ x))

def fixI {F : C ⥤ ModuleCat.{w} R} (S : SubF F) : S.fn ⟶ F where
  app T := ModuleCat.ofHom (S.S T).subtype
  naturality _ _ _ := ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

theorem fixP_fixI {F : C ⥤ ModuleCat.{w} R} (e : F ⟶ F) (he : e ≫ e = e) : fixP e he ≫ fixI (fixF e) = e :=
  NatTrans.ext (funext fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))

def gNat {d : ℕ} (G : SingleObj (Gam d) ⥤ ModuleCat.{w} R) (g : Gam d) : G ⟶ G where
  app _ := G.map (X := SingleObj.star _) (Y := SingleObj.star _) g
  naturality X Y a := by
    rw [← G.map_comp, ← G.map_comp]
    congr 1
    exact mul_comm (g : Gam d) (a : Gam d)

theorem gNat_pull {d : ℕ} (G : SingleObj (Gam d) ⥤ ModuleCat.{w} R) (g : Gam d) (n : ℕ) (x : H G n) :
    (Mor.ofNatTrans (gNat G g)).pull n x = x := by
  have := CrystallineSemistableComparison.P.prism (Mor.ofNatTrans (gNat G g)) (Mor.id G)
    { app := fun _ => (g : SingleObj.star (Gam d) ⟶ SingleObj.star (Gam d)), naturality := fun _ _ a => mul_comm (g : Gam d) (a : Gam d) }
    (fun T x => rfl) n x
  rw [this]
  exact ((CrystallineSemistableComparison.P.pull_comp (Mor.id G) (Mor.id G) n x).2)

theorem killed_of {d : ℕ} (G : SingleObj (Gam d) ⥤ ModuleCat.{w} R) (g : Gam d) (s : R)
    (hu : ∀ T, UpTo s ((gNat G g - 𝟙 G).app T).hom) (n : ℕ) (z : H G n) : s ^ 2 • z = 0 := by
  obtain ⟨x, hx⟩ := (CrystallineSemistableComparison.P.coef_upTo _ s hu n).2 z
  rw [← hx]
  have e1 := ni_pull_add (gNat G g - 𝟙 G) (𝟙 G) n x
  rw [sub_add_cancel, gNat_pull, ni_pull_id] at e1
  calc _ = ((Mor.ofNatTrans (gNat G g - 𝟙 G)).pull n x + x) - x := (add_sub_cancel_right _ _).symm
    _ = x - x := by rw [← e1]
    _ = 0 := sub_self x

theorem ni_killed {d : ℕ} (s : R) {M N : SingleObj (Gam d) ⥤ ModuleCat.{w} R} (α : M ⟶ N) (h : NI s α) (k : Fin d)
    (n : ℕ) (z : H (fixF (h.π k)).fn n) : s ^ 2 • z = 0 := by
  refine killed_of _ (gen k) s (fun T => ?_) n z
  change UpTo s ((gNat (fixF (h.π k)).fn (gen k) - 𝟙 _).app (SingleObj.star _)).hom
  have hδ : ∀ y : (fixF (h.π k)).fn.obj (SingleObj.star _), ((gNat (fixF (h.π k)).fn (gen k) - 𝟙 _).app (SingleObj.star _)).hom y =
      ((fixF (h.π k)).fn.map (X := SingleObj.star _) (Y := SingleObj.star _) (gen k)).hom y - y := fun y => rfl
  refine ⟨fun y hy => ?_, fun y => ?_⟩
  · rw [hδ, sub_eq_zero] at hy
    have h1 : ((h.π k).app _).hom y.1 = y.1 := (mem_fixF (h.π k) _ y.1).1 y.2
    exact Subtype.ext (h.inj k y.1 h1 (congrArg Subtype.val hy))
  · have h1 : ((h.π k).app _).hom y.1 = y.1 := (mem_fixF (h.π k) _ y.1).1 y.2
    obtain ⟨x, hx, hx2⟩ := h.surj k y.1 h1
    exact ⟨⟨x, (mem_fixF (h.π k) _ x).2 hx⟩, by rw [hδ]; exact Subtype.ext hx2⟩

end NiCoh

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.ni_coh : ∀ {R : Type} [CommRing R] {d : ℕ} (s : R) {M N : SingleObj (Gam d) ⥤ ModuleCat.{w} R} (α : M ⟶ N), NI s α → ∀ n, IsoLe (s ^ 2) n (Mor.ofNatTrans α) := by
  intro R _ d s M N α h n j _
  refine ⟨fun x hx => ?_, fun y => ?_⟩
  · have e := ni_pull_comp α h.ρ j x
    rw [h.αρ, ni_pull_id, hx, map_zero] at e
    rw [e, smul_zero]
  · refine ⟨(Mor.ofNatTrans h.ρ).pull j (s ^ 2 • y), ?_⟩
    rw [← ni_pull_comp]
    have e := ni_pull_add (h.ρ ≫ α) (∑ k, h.π k) j (s ^ 2 • y)
    rw [h.sum, ni_pull_id, ni_pull_sum] at e
    have hk : ∀ k, (Mor.ofNatTrans (h.π k)).pull j (s ^ 2 • y) = 0 := by
      intro k
      rw [← fixP_fixI (h.π k) (h.idem k), ni_pull_comp, map_smul, ni_killed s α h k, map_zero]
    rw [Finset.sum_eq_zero (fun k _ => hk k), add_zero] at e
    exact e.symm
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FGlue

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

lemma gl_res_one {R : Type} [CommRing R] {K : Cx.{w} R} {M : Type w'} [AddCommGroup M] [Module R M]
    (ε : M →ₗ[R] K.X 0) (s : R) (h : K.ResUpTo 1 ε) : K.ResUpTo s ε := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine ⟨h0, fun x hx => by rw [← one_smul R x, h1 x hx, smul_zero], fun y hy => ?_, fun m y hy => ?_⟩
  · obtain ⟨x, hx⟩ := h2 y hy
    exact ⟨s • x, by rw [map_smul, hx, one_smul]⟩
  · obtain ⟨x, hx⟩ := h3 m y hy
    exact ⟨s • x, by rw [map_smul, hx, one_smul]⟩

lemma gl_desc_id {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R) (s : R) :
    Desc s F (𝟭 C) := by
  intro T
  have hI : Limits.IsInitial (StructuredArrow.mk (𝟙 T) : StructuredArrow T (𝟭 C)) :=
    StructuredArrow.mkIdInitial (T := 𝟭 C) (Y := T)
  have h := CrystallineSemistableComparison.P.initial (StructuredArrow.proj T (𝟭 C) ⋙ 𝟭 C ⋙ F) _ hI
  have e : (aug (StructuredArrow.proj T (𝟭 C) ⋙ 𝟭 C ⋙ F) fun x =>
      ((StructuredArrow.proj T (𝟭 C) ⋙ 𝟭 C ⋙ F).map (hI.to x)).hom) = unAug F (𝟭 C) T := by
    unfold unAug
    congr 1
    funext x
    have hx : (hI.to x).right = x.hom := by simpa using StructuredArrow.w (hI.to x)
    change (F.map (hI.to x).right).hom = _
    rw [hx]
  rw [← e]
  exact gl_res_one _ s h

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.glue : ∀ d n : ℕ, ∃ N : ℕ, ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {E : Type u'} [Category.{v'} E] {E₀ : Type u''} [Category.{v''} E₀] (F : C ⥤ ModuleCat.{w} R) (G : E ⥤ C) (j : E₀ ⥤ E) [j.Full] [j.Faithful] (U : UF C) (D : C) (A : Act (𝟭 C) U d D) (L : Line (𝟭 C) U) (U' : UF E) (D' : E) (A' : Act j U' d D') (L' : Line j U') (θ : D ⟶ G.obj D') (h : ∀ a, (A.γ a).asHom ≫ θ = θ ≫ G.map (A'.γ a).asHom) (s : R), (∀ T, Acyc1 s (F.map (L.i.app T)).hom (F.map (L.γ.app T)).hom) → Desc s (G ⋙ F) j → (∀ T, Acyc1 s ((G ⋙ F).map (L'.i.app T)).hom ((G ⋙ F).map (L'.γ.app T)).hom) → NI s (Functor.whiskerRight (⟨fun _ => θ, fun _ _ a => h a⟩ : A.ι ⟶ A'.ι ⋙ G) F) → RI (s ^ N) n F (j ⋙ G) := by
  intro d n
  obtain ⟨N₁, h₁⟩ := CrystallineSemistableComparison.B.P.tors.{w, v, u, v, u} d n
  obtain ⟨N₂, h₂⟩ := CrystallineSemistableComparison.B.P.tors.{w, v', u', v'', u''} d n
  refine ⟨N₂ + (N₁ + 2) + (2 * n + 3), ?_⟩
  intro R _ C _ E _ E₀ _ F G j _ _ U D A L U' D' A' L' θ h s hL hD hL' hN
  let θn : A.ι ⟶ A'.ι ⋙ G := ⟨fun _ => θ, fun _ _ a => h a⟩
  have t1 : RI (s ^ N₁) n F A.ι := h₁ F (𝟭 C) U D A L s (gl_desc_id F s) hL
  have t2 : RI (s ^ N₂) n (G ⋙ F) A'.ι := h₂ (G ⋙ F) j U' D' A' L' s hD hL'
  have t3 : RI (s ^ N₁ * s ^ 2) n F (A'.ι ⋙ G) := by
    intro i hi
    have hp : (Mor.restrict F (A'.ι ⋙ G)).pull i =
        ((Mor.ofNatTrans (Functor.whiskerRight θn F)).pull i).comp ((Mor.restrict F A.ι).pull i) := by
      rw [← rc_pull_comp]
      exact (LinearMap.ext fun x => CrystallineSemistableComparison.P.prism ((Mor.restrict F A.ι).comp (Mor.ofNatTrans (Functor.whiskerRight θn F)))
        (Mor.restrict F (A'.ι ⋙ G)) θn (fun T x => rfl) i x).symm
    rw [hp]
    exact (CrystallineSemistableComparison.P.upTo_alg _ _ _ _).1 (t1 i hi) (P.ni_coh s (Functor.whiskerRight θn F) hN n i hi)
  have t4 : RI (s ^ N₂ * (s ^ N₁ * s ^ 2)) n F G := (P.ri_calc F G A'.ι _ _ n).2.2.1 t2 t3
  have t5 : RI (s ^ (2 * n + 3)) n (G ⋙ F) j := P.fib (Mor.restrict (G ⋙ F) j) s hD n
  have t6 := (P.ri_calc F G j _ _ n).1 t4 t5
  have he : s ^ (N₂ + (N₁ + 2) + (2 * n + 3)) = s ^ N₂ * (s ^ N₁ * s ^ 2) * s ^ (2 * n + 3) := by ring
  rw [he]
  exact t6
end
end
