module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBidualNaturalityDualSheafTranspose

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self val_res homOfLinear homOfLinear_app isoOfLinear toMod fun_ext_of_cover exists_fun_of_cover)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM sec_ext_of_cover exists_sec_of_cover germ_resM)
open GlobalTheory.QCoh (IsFiniteQC appLinear appLinear_apply stalkLinear freeModule)

namespace GlobalTheory.VB

open scoped TensorProduct

variable {X Y : Scheme.{0}} {F G H : X.Modules} {U V W : X.Opens}

section Eigen

variable {O : Type} [CommRing O] (ρ : O →+* End F) (ρ' : O →+* End G) (ρ'' : O →+* End H)
  (σ : O →+* Γ(X, ⊤))

abbrev act (a : O) : F ⟶ F := ρ a

def ActsThrough : Prop := ∀ a, act ρ a = smulHom F (σ a)

def IsEquivariant (φ : F ⟶ G) : Prop := ∀ a, act ρ a ≫ φ = φ ≫ act ρ' a

def eigenSub : Sub F := Sub.iInf fun a => Sub.ker (act ρ a - smulHom F (σ a))

def eigen : X.Modules := (eigenSub ρ σ).toMod

def eigenι : eigen ρ σ ⟶ F := (eigenSub ρ σ).incl


theorem mem_eigenSub_iff {s : Γ(F, V)} : s ∈ (eigenSub ρ σ).sec V ↔
    ∀ a, (act ρ a).app V s = resG X (le_top : V ≤ ⊤) (σ a) • s :=
  (Submodule.mem_iInf _).trans (forall_congr' fun _ => sub_eq_zero)


def eigenLift (φ : G ⟶ F) (h : ∀ a, φ ≫ act ρ a = σ a • φ) : G ⟶ eigen ρ σ :=
  (eigenSub ρ σ).lift φ fun V s => mem_eigenSub_iff.2 fun a => congr(($(h a)).app V s)

    eigenLift φ h ≫ eigenι ρ σ = φ := rfl





def scalarAct : O →+* End F := (smulEnd F).comp σ

def eigenQuot : X.Modules :=
  cokernel (Sigma.desc fun a : O => act ρ a - smulHom F (σ a) : ∐ (fun _ : O => F) ⟶ F)

def eigenπ : F ⟶ eigenQuot ρ σ := cokernel.π _

instance epi_eigenπ : Epi (eigenπ ρ σ) := inferInstanceAs (Epi (cokernel.π _))

theorem act_eigenπ (a : O) : act ρ a ≫ eigenπ ρ σ = σ a • eigenπ ρ σ := by
  have := Sigma.ι (fun _ : O => F) a ≫= cokernel.condition
    (Sigma.desc fun a : O => act ρ a - smulHom F (σ a) : ∐ (fun _ : O => F) ⟶ F)
  rw [Sigma.ι_desc_assoc, comp_zero, Preadditive.sub_comp, sub_eq_zero, smulHom_comp] at this
  exact this


def eigenDesc (φ : F ⟶ G) (h : ∀ a, act ρ a ≫ φ = σ a • φ) : eigenQuot ρ σ ⟶ G :=
  cokernel.desc _ φ (Sigma.hom_ext _ _ fun a => by
    rw [Sigma.ι_desc_assoc, comp_zero, Preadditive.sub_comp, h a, smulHom_comp]
    exact sub_self _)

@[reassoc (attr := simp)] theorem eigenπ_desc (φ : F ⟶ G) (h : ∀ a, act ρ a ≫ φ = σ a • φ) :
    eigenπ ρ σ ≫ eigenDesc φ h = φ := cokernel.π_desc _ _ _

def dualAct : O →+* End (dual F) where
  toFun a := GlobalTheory.CompanionTheory.Ar.dualMap (act ρ a)
  map_one' := by rw [act, map_one]; exact dualMap_id
  map_mul' a b := by rw [act, mul_comm, map_mul]; exact dualMap_comp _ _
  map_zero' := by rw [act, map_zero]; exact dualMap_zero
  map_add' a b := by rw [act, map_add (f := _)]; exact dualMap_add _ _

@[simp] theorem act_dualAct (a : O) : act (dualAct ρ) a = GlobalTheory.CompanionTheory.Ar.dualMap (act ρ a) := rfl


theorem ActsThrough.dual (h : ActsThrough ρ σ) : ActsThrough (dualAct ρ) σ := fun a => by
  rw [act_dualAct, h a, dualMap_smulHom]


theorem pullback_map_smulHom (f : Y ⟶ X) (a : Γ(X, ⊤)) :
    (Scheme.Modules.pullback f).map (smulHom F a) = smulHom _ (f.appTop a) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, pushforward_map_smulHom]
  exact ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality _).symm.trans
    (smulHom_comp _ _)

theorem pullback_map_smul (f : Y ⟶ X) (a : Γ(X, ⊤)) (φ : F ⟶ G) :
    (Scheme.Modules.pullback f).map (a • φ) =
      (f.appTop a : Γ(Y, ⊤)) • (Scheme.Modules.pullback f).map φ := by
  rw [smul_hom_def, smul_hom_def, Functor.map_comp, pullback_map_smulHom]

def pullAct (f : Y ⟶ X) : O →+* End ((Scheme.Modules.pullback f).obj F) where
  toFun a := (Scheme.Modules.pullback f).map (act ρ a)
  map_one' := by rw [act, map_one]; exact CategoryTheory.Functor.map_id _ _
  map_mul' a b := by rw [act, map_mul]; exact Functor.map_comp _ _ _
  map_zero' := by rw [act, map_zero]; exact Functor.map_zero _ _ _
  map_add' a b := by rw [act, map_add (f := _)]; exact Functor.map_add _

@[simp] theorem act_pullAct (f : Y ⟶ X) (a : O) :
    act (pullAct ρ f) a = (Scheme.Modules.pullback f).map (act ρ a) := rfl


theorem ActsThrough.pullback (h : ActsThrough ρ σ) (f : Y ⟶ X) :
    ActsThrough (pullAct ρ f) (f.appTop.hom.comp σ) := fun a => by
  rw [act_pullAct, h a, pullback_map_smulHom]; rfl


end Eigen

section Split

variable {O : Type} [CommRing O] {k : Type} [Field k] {ι : Type}


abbrev scal [Algebra k Γ(X, ⊤)] (σ : O →+* k) : O →+* Γ(X, ⊤) := (algebraMap k Γ(X, ⊤)).comp σ

def splitMap (σ : ι → (O →+* k)) : k ⊗[ℤ] O →ₐ[k] (ι → k) :=
  Algebra.TensorProduct.lift (Algebra.ofId k (ι → k)) (Pi.ringHom σ).toIntAlgHom
    fun _ _ => Commute.all _ _

def IsSplitBy (σ : ι → (O →+* k)) : Prop := Function.Bijective (splitMap σ)

variable {σ : ι → (O →+* k)}

theorem isSplitBy_of_injective [Fintype ι] [Module.Free ℤ O] [Module.Finite ℤ O]
    (hσ : Function.Injective σ) (hn : Module.finrank ℤ O = Fintype.card ι) : IsSplitBy σ := by
  have hs : Function.Surjective (splitMap σ).toLinearMap := by
    have hl : LinearIndependent k fun j => (σ j : O → k) :=
      (linearIndependent_monoidHom O k).comp (fun j => (σ j : O →* k))
        fun i j e => hσ (RingHom.ext fun a => DFunLike.congr_fun (F := O →* k) e a)
    rw [← LinearMap.range_eq_top, eq_top_iff, ← span_flip_eq_top_iff_linearIndependent.2 hl,
      Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact ⟨1 ⊗ₜ a, funext fun j => one_mul _⟩
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hn])).2 hs, hs⟩

variable [Algebra k Γ(X, ⊤)] (ρ : O →+* End F)


namespace IsSplitBy

variable [DecidableEq ι] (h : IsSplitBy σ)

variable [Fintype ι]



end IsSplitBy

end Split

section Frobenius

variable (p : ℕ) [Fact p.Prime]


def frob (h : (p : Γ(X, ⊤)) = 0) : X ⟶ X := SS.FrobField.absFrob X p 1 Fact.out h

variable (h : (p : Γ(X, ⊤)) = 0)

theorem frob_app (U : X.Opens) (a : Γ(X, U)) : (frob X p h).app U a = (a ^ p : Γ(X, U)) :=
  congrArg (a ^ ·) (pow_one p)

theorem frob_appTop (a : Γ(X, ⊤)) : (frob X p h).appTop a = a ^ p := frob_app p h ⊤ a

    frob Y p hY ≫ f = f ≫ frob X p h := SS.FrobField.absFrob_nat f p 1 Fact.out hY h


theorem natCast_eq_zero (k : Type) [CommRing k] [CharP k p] [Algebra k Γ(X, ⊤)] :
    (p : Γ(X, ⊤)) = 0 := by
  rw [← map_natCast (algebraMap k Γ(X, ⊤)), CharP.cast_eq_zero, map_zero]

abbrev frobPull : X.Modules ⥤ X.Modules := Scheme.Modules.pullback (frob X p h)

theorem IsVB.frobPull {r : ℕ} (hF : IsVB F r) : IsVB ((frobPull p h).obj F) r := hF.pullback _

variable {O : Type} [CommRing O] {k : Type} [Field k] [CharP k p] [Algebra k Γ(X, ⊤)]

theorem frob_comp_scal (σ : O →+* k) :
    (frob X p h).appTop.hom.comp (scal X σ) = scal X ((frobenius k p).comp σ) :=
  RingHom.ext fun a => (frob_appTop p h _).trans (map_pow (algebraMap k Γ(X, ⊤)) (σ a) p).symm

theorem ActsThrough.frobPull {ρ : O →+* End F} {σ : O →+* k} (hρ : ActsThrough ρ (scal X σ)) :
    ActsThrough (pullAct ρ (frob X p h)) (scal X ((frobenius k p).comp σ)) :=
  frob_comp_scal p h σ ▸ hρ.pullback _

end Frobenius

end GlobalTheory.VB
