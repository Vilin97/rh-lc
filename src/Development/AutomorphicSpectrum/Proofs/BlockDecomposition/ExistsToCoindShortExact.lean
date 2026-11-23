module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CubeResApply
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.TopologicalKrullDimLeOfIrreducibleCloseds
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsPowMulPowEqOfIsZeroCechH
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechStructureSheafComparison
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoinducedCechAcyclicStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoinducedNerveAcyclicStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NaturalDegreeZeroHomologyIsoStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NerveCechDegreeZeroCompatible
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechStructureSheafComparisonStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve

theorem _root_.GlobalTheory.T.cech_structure_sheaf_comparison : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of R)) (P : Type) [SemilatticeInf P]
    (S : MainStatements.Hodge.Sys X P) {κ : Type} [LinearOrder κ] (e : κ → P) (n : ℕ),
    letI := GlobalTheory.algebraΓOfHom s
    Nonempty (((cechOf e).obj (toMod (MainStatements.Hodge.OSys s S))).homology n ≃ₗ[R]
      GlobalTheory.cechH R (GlobalTheory.structureModule X) ⊤ (fun i ↦ (S.u (e i)).1) n) :=
  @cech_OSys_homology_equiv
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CochainCohomologyNerveHomologyEquiv

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve

namespace GlobalTheory.CompanionTheory.Hodge.Nerve.Low

variable {R : Type} [CommRing R]

theorem homology_equiv {A B D : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup D] [Module R A] [Module R B]
    [Module R D] (a : A →ₗ[R] B) (b : B →ₗ[R] D)
    (w : ModuleCat.ofHom a ≫ ModuleCat.ofHom b = 0) :
    Nonempty ((LinearMap.ker b ⧸ (LinearMap.range a).comap (LinearMap.ker b).subtype) ≃ₗ[R]
      (ShortComplex.mk (ModuleCat.ofHom a) (ModuleCat.ofHom b) w).homology) := by
  have heq : (LinearMap.range a).comap (LinearMap.ker b).subtype =
      LinearMap.range (ShortComplex.mk (ModuleCat.ofHom a) (ModuleCat.ofHom b) w).moduleCatToCycles := by
    ext x
    simp only [Submodule.mem_comap, Submodule.coe_subtype, LinearMap.mem_range]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, Subtype.ext hy⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, rfl⟩
  exact ⟨(Submodule.quotEquivOfEq _ _ heq).trans
    (ShortComplex.mk (ModuleCat.ofHom a) (ModuleCat.ofHom b) w).moduleCatHomologyIso.symm.toLinearEquiv⟩

variable {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

abbrev nerveComplex : CochainComplex (ModuleCat.{0} R) ℕ :=
  nerveCx.obj (F ⋙ forget₂ (CommAlgCat.{0} R) (AlgCat.{0} R) ⋙ forget₂ (AlgCat.{0} R) (ModuleCat.{0} R))

theorem d_eq (n : ℕ) : (nerveComplex F).d n (n + 1) = ModuleCat.ofHom (MainStatements.Hodge.dn F n) :=
  nerveCx_d _ n

theorem d_zero : (nerveComplex F).d 0 0 = ModuleCat.ofHom (0 : MainStatements.Hodge.Cn F 0 →ₗ[R] MainStatements.Hodge.Cn F 0) :=
  ((nerveComplex F).shape 0 0 (by simp)).trans ModuleCat.ofHom_zero.symm

theorem comp_eq (n : ℕ) :
    ModuleCat.ofHom (MainStatements.Hodge.dn F n) ≫ ModuleCat.ofHom (MainStatements.Hodge.dn F (n + 1)) = 0 := by
  simpa only [d_eq] using! (nerveComplex F).d_comp_d n (n + 1) (n + 1 + 1)

theorem comp_zero_eq :
    ModuleCat.ofHom (0 : MainStatements.Hodge.Cn F 0 →ₗ[R] MainStatements.Hodge.Cn F 0) ≫ ModuleCat.ofHom (MainStatements.Hodge.dn F 0) = 0 := by
  rw [ModuleCat.ofHom_zero, zero_comp]

def scIso (n : ℕ) : (nerveComplex F).sc' n (n + 1) (n + 2) ≅
    ShortComplex.mk (ModuleCat.ofHom (MainStatements.Hodge.dn F n)) (ModuleCat.ofHom (MainStatements.Hodge.dn F (n + 1))) (comp_eq F n) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans ((d_eq F n).symm.trans (Category.comp_id _).symm))
    ((Category.id_comp _).trans ((d_eq F (n + 1)).symm.trans (Category.comp_id _).symm))

def scIso0 : (nerveComplex F).sc' 0 0 1 ≅
    ShortComplex.mk (ModuleCat.ofHom (0 : MainStatements.Hodge.Cn F 0 →ₗ[R] MainStatements.Hodge.Cn F 0)) (ModuleCat.ofHom (MainStatements.Hodge.dn F 0))
      (comp_zero_eq F) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans ((d_zero F).symm.trans (Category.comp_id _).symm))
    ((Category.id_comp _).trans ((d_eq F 0).symm.trans (Category.comp_id _).symm))

theorem homology_nerveCx :
    ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    Nonempty (LinearMap.ker (MainStatements.Hodge.dn F 0) ≃ₗ[R] (nerveComplex F).homology 0) ∧
      ∀ n, Nonempty (MainStatements.Hodge.Hs F n ≃ₗ[R] (nerveComplex F).homology (n + 1)) := by
  intro R _ C _ F
  refine ⟨?_, fun n => ?_⟩
  · obtain ⟨e⟩ := GlobalTheory.CompanionTheory.Hodge.Nerve.Low.homology_equiv
      (0 : MainStatements.Hodge.Cn F 0 →ₗ[R] MainStatements.Hodge.Cn F 0)
      (MainStatements.Hodge.dn F 0) (GlobalTheory.CompanionTheory.Hodge.Nerve.Low.comp_zero_eq F)
    have hbot : (LinearMap.range (0 : MainStatements.Hodge.Cn F 0 →ₗ[R]
        MainStatements.Hodge.Cn F 0)).comap
        (LinearMap.ker (MainStatements.Hodge.dn F 0)).subtype = ⊥ := by
      simp
    exact ⟨((Submodule.quotEquivOfEqBot _ hbot).symm.trans e).trans
      (((nerveComplex F).homologyIsoSc'
        0 0 1 (by simp) (by simp)) ≪≫
        ShortComplex.homologyMapIso (GlobalTheory.CompanionTheory.Hodge.Nerve.Low.scIso0 F)).symm.toLinearEquiv⟩
  · obtain ⟨e⟩ := GlobalTheory.CompanionTheory.Hodge.Nerve.Low.homology_equiv
      (MainStatements.Hodge.dn F n) (MainStatements.Hodge.dn F (n + 1))
      (GlobalTheory.CompanionTheory.Hodge.Nerve.Low.comp_eq F n)
    exact ⟨e.trans
      (((nerveComplex F).homologyIsoSc'
        n (n + 1) (n + 2) (by simp) (by simp)) ≪≫
        ShortComplex.homologyMapIso (GlobalTheory.CompanionTheory.Hodge.Nerve.Low.scIso F n)).symm.toLinearEquiv⟩

end GlobalTheory.CompanionTheory.Hodge.Nerve.Low
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CochainCohomologyNerveHomologyEquivStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve

theorem _root_.GlobalTheory.T.cochain_cohomology_nerve_homology_equiv : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    Nonempty (LinearMap.ker (MainStatements.Hodge.dn F 0) ≃ₗ[R] (nerveCx.obj (toMod F)).homology 0) ∧
      ∀ n, Nonempty (MainStatements.Hodge.Hs F n ≃ₗ[R] (nerveCx.obj (toMod F)).homology (n + 1)) :=
  @GlobalTheory.CompanionTheory.Hodge.Nerve.Low.homology_nerveCx
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NerveCechDegreeZeroCompatibleStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve

theorem _root_.GlobalTheory.T.nerve_cech_degree_zero_compatible : ∀ {R : Type} [CommRing R] {P : Type} [SemilatticeInf P] {κ : Type} [LinearOrder κ] (e : κ → P),
    Function.Bijective e → ∃ ε : ∀ G : Pᵒᵖ ⥤ ModuleCat.{0} R, (nerveCx.obj G).X 0 ≅ ((cechOf e).obj G).X 0,
    (∀ {G G' : Pᵒᵖ ⥤ ModuleCat.{0} R} (φ : G ⟶ G'),
      (nerveCx.map φ).f 0 ≫ (ε G').hom = (ε G).hom ≫ ((cechOf e).map φ).f 0) ∧
    ∀ (G : Pᵒᵖ ⥤ ModuleCat.{0} R) (x : (nerveCx.obj G).X 0),
      ((nerveCx.obj G).d 0 1).hom x = 0 ↔ (((cechOf e).obj G).d 0 1).hom ((ε G).hom.hom x) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Hodge.Nerve.DegZero.degZero | exact GlobalTheory.CompanionTheory.Hodge.Nerve.DegZero.degZero | (intros; apply GlobalTheory.CompanionTheory.Hodge.Nerve.DegZero.degZero <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsToCoindShortExact

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.Hodge.Nerve

theorem nerveCx_shortExact {R : Type} [CommRing R] {C : Type} [Category.{0} C]
    (S : ShortComplex (C ⥤ ModuleCat.{0} R))
    (hS : ∀ a : C, (S.map ((evaluation _ _).obj a)).ShortExact) : (S.map nerveCx).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun p ↦ ?_
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · change Function.Exact ((nerveCx.map S.f).f p).hom ((nerveCx.map S.g).f p).hom
    have h := fun a : C ↦ (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (hS a).exact
    intro y
    constructor
    · intro hy
      choose x hx using fun c : Fin (p + 1) ⥤ C ↦ (h _ (y c)).1 (congrFun hy c)
      exact ⟨x, funext hx⟩
    · rintro ⟨x, rfl⟩
      exact funext fun c ↦ (h _ _).2 ⟨x c, rfl⟩
  · change Function.Injective ((nerveCx.map S.f).f p).hom
    exact fun x y hxy ↦ funext fun c ↦ (hS _).moduleCat_injective_f (congrFun hxy c)
  · change Function.Surjective ((nerveCx.map S.g).f p).hom
    intro y
    choose x hx using fun c : Fin (p + 1) ⥤ C ↦ (hS _).moduleCat_surjective_g (y c)
    exact ⟨x, funext hx⟩

theorem cechOf_shortExact {R : Type} [CommRing R] {P : Type} [SemilatticeInf P] {κ : Type} [LinearOrder κ] (e : κ → P)
    (S : ShortComplex (Pᵒᵖ ⥤ ModuleCat.{0} R))
    (hS : ∀ a : Pᵒᵖ, (S.map ((evaluation _ _).obj a)).ShortExact) : (S.map (cechOf e)).ShortExact := by
  refine (cechFunctor_shortExact (S.map (cubeOfFunctor e)) fun s hs ↦ ?_ : ((S.map (cubeOfFunctor e)).map (cechFunctor κ R)).ShortExact)
  have hs' : ∀ (hs : PLift s.Nonempty), _ := fun hs : PLift s.Nonempty ↦ hS (op (s.inf' hs.down e))
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · intro y
    have h := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (hs' ⟨hs⟩).exact
    constructor
    · intro hy
      obtain ⟨x, hx⟩ := (h (y ⟨hs⟩)).1 (congrFun hy ⟨hs⟩)
      exact ⟨fun _ ↦ x, funext fun _ ↦ hx⟩
    · rintro ⟨x, rfl⟩
      exact funext fun t ↦ (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (hs' t).exact _ |>.2 ⟨x t, rfl⟩
  · exact fun x y hxy ↦ funext fun t ↦ (hs' t).moduleCat_injective_f (congrFun hxy t)
  · intro y
    choose x hx using fun t : PLift s.Nonempty ↦ (hs' t).moduleCat_surjective_g (y t)
    exact ⟨x, funext hx⟩

theorem exists_toCoind_shortExact {R : Type} [CommRing R] {P : Type} [SemilatticeInf P]
    (G : Pᵒᵖ ⥤ ModuleCat.{0} R) :
    ∃ (Q : Pᵒᵖ ⥤ ModuleCat.{0} R) (p : (coind fun b ↦ G.obj (op b)) ⟶ Q) (w : toCoind G ≫ p = 0),
      ∀ a : Pᵒᵖ, ((ShortComplex.mk _ _ w).map ((evaluation _ _).obj a)).ShortExact := by
  have : Mono (toCoind G) := by
    refine (NatTrans.mono_iff_mono_app _).2 fun a ↦ (ModuleCat.mono_iff_injective _).2 fun x y h ↦ ?_
    have h1 := congrFun h ⟨a.unop, le_rfl⟩
    have e : ∀ z : G.obj a, (G.map (homOfLE (le_refl a.unop)).op).hom z = z := fun z ↦ by
      have : (homOfLE (le_refl a.unop)).op = 𝟙 a := rfl
      rw [this, G.map_id]
      rfl
    exact (e x).symm.trans (h1.trans (e y))
  have hS : (ShortComplex.mk _ _ (cokernel.condition (toCoind G))).ShortExact :=
    { exact := ShortComplex.exact_cokernel _ }
  exact ⟨_, _, _, fun a ↦ hS.map_of_exact _⟩

theorem nonempty_iso {R : Type} [CommRing R] {P : Type} [SemilatticeInf P] {κ : Type} [LinearOrder κ] (e : κ → P)
    (he : Function.Bijective e) (n : ℕ) (G : Pᵒᵖ ⥤ ModuleCat.{0} R) :
    Nonempty ((nerveCx.obj G).homology n ≅ ((cechOf e).obj G).homology n) := by
  obtain ⟨ε, h1, h2⟩ := GlobalTheory.T.nerve_cech_degree_zero_compatible (R := R) e he
  refine GlobalTheory.T.natural_degree_zero_homology_iso nerveCx (cechOf e) ε h1 h2 (fun G ↦ ?_) n G
  obtain ⟨Q, p, w, h⟩ := exists_toCoind_shortExact G
  exact ⟨_, Q, toCoind G, p, w, nerveCx_shortExact _ h, cechOf_shortExact e _ h,
    fun n ↦ ⟨GlobalTheory.T.coinduced_nerve_acyclic _ n, GlobalTheory.T.coinduced_cech_acyclic e he.2 _ n⟩⟩


theorem cmpSt_of_cxSt : CxSt → CmpSt := by
  intro _ R _ X s _ P _ _ S
  letI := GlobalTheory.algebraΓOfHom s
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin P
  let e' : Fin m → P := e.symm
  have he' : Function.Bijective e' := e.symm.bijective
  have hc : ⨆ i, (S.u (e' i)).1 = ⊤ := by
    rw [← S.cover]
    exact e.symm.iSup_comp (g := fun a ↦ (S.u a).1)
  have hinf : ∀ (t : Finset (Fin m)) (ht : t.Nonempty), (⨅ i ∈ t, (S.u (e' i)).1) = (S.u (t.inf' ht e')).1 := by
    intro t ht
    induction ht using Finset.Nonempty.cons_induction with
    | singleton i => simp
    | cons i t hi ht ih =>
      rw [Finset.inf'_cons ht, S.map_inf, Finset.cons_eq_insert, Finset.iInf_insert, ih]
  have hD : ∀ t : Finset (Fin m), t.Nonempty → IsAffineOpen (⨅ i ∈ t, (S.u (e' i)).1) := fun t ht ↦ by
    rw [hinf t ht]
    exact (S.u _).2
  have key : ∀ n, Nonempty ((nerveCx.obj (toMod (OSys s S))).homology n ≃ₗ[R] GlobalTheory.coh (GlobalTheory.structureModule X) n) := by
    intro n
    obtain ⟨i⟩ := nonempty_iso e' he' n (toMod (OSys s S))
    obtain ⟨f⟩ := GlobalTheory.T.cech_structure_sheaf_comparison R X s P S e' n
    letI : (GlobalTheory.structureModule X).IsQuasicoherent := GlobalTheory.QCoh.IsFiniteQC.isQuasicoherent
    exact ⟨i.toLinearEquiv ≪≫ₗ f ≪≫ₗ GlobalTheory.cechHEquivCoh R hc hD (GlobalTheory.structureModule X) n⟩
  obtain ⟨⟨a⟩, b⟩ := GlobalTheory.T.cochain_cohomology_nerve_homology_equiv (OSys s S)
  obtain ⟨k⟩ := key 0
  refine ⟨⟨a ≪≫ₗ k⟩, fun n ↦ ?_⟩
  obtain ⟨b'⟩ := b n
  obtain ⟨k'⟩ := key (n + 1)
  exact ⟨b' ≪≫ₗ k'⟩

end GlobalTheory.CompanionTheory.Hodge.Nerve
end
end
end
