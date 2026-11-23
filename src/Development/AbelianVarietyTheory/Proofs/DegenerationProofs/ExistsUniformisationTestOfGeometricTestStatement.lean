module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIntegralOfWeightZeroCoordinateDominatesStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LePreimageOpenPartIffTestCoordinatesStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsClosedImmersionTestSpecialFibreOpenPartStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestFieldFiniteOverPadicStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestModelMapsIntoOpenPartStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedTestDimensionsAndSplitFibreStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftIntegralPointClosureTestModel

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ClosLift

theorem isDominant_gPt (p : ℕ) [Fact p.Prime] : IsDominant (gPt p) := by
  refine ⟨?_⟩
  change DenseRange (PrimeSpectrum.comap (OO p).subtype)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot _).1 (OO p).subtype_injective]
  exact bot_le

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real}

theorem big (ρ : S.Real) (h : S.Big) : Big S.g S.N (S.r * S.N) := by
  refine ⟨?_, h.1, h.2.1⟩
  rw [ρ.N_eq]
  have h1 : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
  nlinarith

theorem gPt_j {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) :
    gPt p ≫ spMap u.j = spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V :=
  (spMap_comp' _ _).trans (spMap_comp' (algebraMap u.V (FractionRing u.V)) (algebraMap (FractionRing u.V) (PadicAlgCl p))).symm

theorem exists_generic {M : RatModel o Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} {Q : Clos ρ M U₀ EE} {p : ℕ}
    [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} {y₀ : S.R →+* PadicAlgCl p} {t : ρ.GeoTest p y₀} {c : Q.Fac y t.u}
    (tm : Q.TMap t c) (x : Sp (PadicAlgCl p) ⟶ Q.P.left) (hx : x ≫ Q.P.hom = gPt p ≫ y) :
    ∃ a : Sp (PadicAlgCl p) ⟶ t.u.G.left, a ≫ t.u.G.hom = gPt p ≫ spMap t.u.j ∧
      a ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = x := by
  set κ := spMap (algebraMap (FractionRing t.u.V) (PadicAlgCl p)) with hκ
  have h1 : x ≫ Q.P.hom = (κ ≫ c.yK) ≫ U₀.ι := by
    rw [hx, Category.assoc, c.yK_fac, ← Category.assoc, ← gPt_j, Category.assoc, c.fac]
  let a1 := Q.cart.lift x (κ ≫ c.yK) h1
  have e1 : a1 ≫ Q.a₀ = x := Q.cart.lift_fst _ _ _
  have e2 : a1 ≫ pullback.snd _ _ = κ ≫ c.yK := Q.cart.lift_snd _ _ _
  have h2 : (a1 ≫ pullback.fst _ _) ≫ ρ.P.A.hom = κ ≫ spMap t.u.yK := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, e2, Category.assoc, c.yK_u]
  let a2 := t.u.cart.1.lift (a1 ≫ pullback.fst _ _) κ h2
  have e3 : a2 ≫ t.u.φ = a1 ≫ pullback.fst _ _ := t.u.cart.1.lift_fst _ _ _
  have e4 : a2 ≫ t.u.A.A.hom = κ := t.u.cart.1.lift_snd _ _ _
  let a3 : Sp (PadicAlgCl p) ⟶ pullback t.u.G.hom (jK t.u.V) := a2 ≫ t.u.U.gen.inv.left
  have e5 : a3 ≫ pullback.snd _ _ = κ := by
    rw [← e4]
    exact (Category.assoc _ _ _).trans (congrArg (a2 ≫ ·) (Over.w t.u.U.gen.inv))
  have e6 : a3 ≫ t.u.U.gen.hom.left = a2 := by
    refine (Category.assoc _ _ _).trans ((congrArg (a2 ≫ ·) ?_).trans (Category.comp_id _))
    exact congrArg CommaMorphism.left t.u.U.gen.inv_hom_id
  have e7 : a3 ≫ tm.φ = a1 := by
    apply pullback.hom_ext
    · rw [Category.assoc, tm.φ_fst, ← e3, ← e6]
      exact (Category.assoc _ _ _).symm
    · rw [Category.assoc, tm.φ_snd, ← Category.assoc, e5, e2]
  refine ⟨a3 ≫ pullback.fst _ _, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, e5, gPt_j]
  · rw [Category.assoc, ← tm.φ_f, ← Category.assoc, e7, e1]

theorem exists_lift : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ∀ b : Sp (OO p) ⟶ Q.P.left, b ≫ Q.P.hom = y → ⊤ ≤ b ⁻¹ᵁ Q.G → ∃ c' : Sp (OO p) ⟶ t.u.G.left, c' ≫ t.u.G.hom = spMap t.u.j ∧ c' ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = b := by
  intro _ o Ω _ _ _ _ S ρ M U₀ EE hB Q p _ y y₀ t c tm hbig b hb hG
  have hW : ⊤ ≤ b ⁻¹ᵁ (Q.P.hom ⁻¹ᵁ Q.W tm.l) := by
    rw [← Scheme.Hom.comp_preimage, hb]
    exact (CrdCalc.top_le_iff y _).2 tm.mem
  obtain ⟨b', hb'⟩ : ∃ b' : Sp (OO p) ⟶ (Q.P.hom ⁻¹ᵁ Q.W tm.l).toScheme, b' ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = b :=
    ⟨IsOpenImmersion.lift _ b (by
      rw [Scheme.Opens.range_ι]; exact (top_le_preimage_iff _ _).1 hW), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨w', hw'⟩ := CrdCalc.crd_exists (pull_isLB Q.isLB (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) (Q.σ tm.l) b'
  have hdet : ∀ {R : Type} [CommRing R] (ψ : t.u.V →+* R), IsUnit (tm.m.map ψ).det := fun ψ => by
    have := tm.unit.map ψ
    rwa [RingHom.map_det] at this
  obtain ⟨w, rfl⟩ : ∃ w, w' = (tm.m.map t.u.j).mulVec w :=
    ⟨(tm.m.map t.u.j)⁻¹.mulVec w', by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hdet _), Matrix.one_mulVec]⟩
  have hmap : ∀ {R : Type} [CommRing R] (ψ : OO p →+* R), Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) (Q.σ tm.l)
      (spMap ψ ≫ b') ((tm.m.map (ψ.comp t.u.j)).mulVec fun i => ψ (w i)) := fun ψ => by
    have := CrdCalc.crd_map ψ hw'
    refine (congrArg _ (funext fun i => ?_)).mp this
    exact RingHom.map_mulVec ψ _ _ i
  obtain ⟨i₀, hi₀, hne⟩ := (GlobalTheory.T.le_preimage_openPart_iff_testCoordinates o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hbig (rPt p ≫ b')
    (fun i => IsLocalRing.residue (OO p) (w i))
    (by rw [Category.assoc, ← Category.assoc b', hb', hb]) (hmap _)).1 (by
      rw [Category.assoc, hb']
      exact fun z _ => hG (Set.mem_univ (rPt p z)))
  have hu : IsUnit (w i₀) := (IsLocalRing.residue_ne_zero_iff_isUnit _).1 hne
  have hn : 1 ≤ ‖(w i₀ : PadicAlgCl p)‖ := not_lt.1 fun h => (not_isUnit_OO_iff _).2 h hu
  obtain ⟨a, ha, haf⟩ := exists_generic tm (gPt p ≫ b) (by rw [Category.assoc, hb])
  have haf' : a ≫ tm.f = gPt p ≫ b' := by
    rw [← cancel_mono (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι, Category.assoc, haf, Category.assoc, hb']
  obtain ⟨v, hv⟩ := CrdCalc.crd_exists t.mod.isLB t.σ a
  have h1 := tm.crd _ ((OO p).subtype.comp t.u.j) a v (ha.trans (spMap_comp' _ _)) hv
  rw [haf'] at h1
  obtain ⟨κ, hκ⟩ := CrdCalc.crd_unique h1 (hmap (OO p).subtype)
  have h2 : (fun i => (OO p).subtype (w i)) = fun i => (κ : PadicAlgCl p) * v i := by
    refine Matrix.mulVec_injective_iff_isUnit.2
      ((Matrix.isUnit_iff_isUnit_det _).2 (hdet ((OO p).subtype.comp t.u.j))) ?_
    have : (fun i => (κ : PadicAlgCl p) * v i) = (κ : PadicAlgCl p) • v := rfl
    rw [this, Matrix.mulVec_smul]
    exact funext hκ
  have h3 := CrdCalc.crd_smul κ hv
  rw [← h2] at h3
  obtain ⟨c', hc', hc''⟩ := GlobalTheory.T.isIntegral_of_weightZeroCoordinate_dominates p t.u.V t.u.j t.u.G S.g S.N (S.r * S.N) _ t.l.q _ S.J t.σ t.cls t.mod
    (big ρ hbig) a _ ha h3 ⟨i₀, hi₀, fun i => ((mem_OO_iff _).1 (w i).2).trans hn⟩
  refine ⟨c', hc', ?_⟩
  have := isDominant_gPt p
  have := Q.proper
  refine ext_of_isDominant_of_isSeparated Q.P.hom ?_ (gPt p) ?_
  · rw [Category.assoc, Category.assoc, tm.f_over, ← Category.assoc, hc', c.fac, hb]
  · rw [← Category.assoc, hc'', haf]

end GlobalTheory.ZH.ClosLift
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftIntegralPointClosureTestModelStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.exists_lift_integralPoint_closure_testModel : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ∀ b : Sp (OO p) ⟶ Q.P.left, b ≫ Q.P.hom = y → ⊤ ≤ b ⁻¹ᵁ Q.G → ∃ c' : Sp (OO p) ⟶ t.u.G.left, c' ≫ t.u.G.hom = spMap t.u.j ∧ c' ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = b := by
  first | exact @GlobalTheory.ZH.ClosLift.exists_lift | exact GlobalTheory.ZH.ClosLift.exists_lift | (intros; apply GlobalTheory.ZH.ClosLift.exists_lift <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationTestOfGeometricTest

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem Clos.exists_core_test_of_geoTest : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext) (p : ℕ) [Fact p.Prime] (y : Sp (GlobalTheory.ZJ.OO p) ⟶ ex.core.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ∃ (τ : ex.core.Test y) (e : pullback τ.H.hom (GlobalTheory.ZJ.rPt p ≫ spMap τ.j) ≅ t.mod.Φ.G.left), e.hom ≫ t.mod.Φ.G.hom = pullback.snd _ _ ∧ e.hom ≫ t.mod.r ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = pullback.fst _ _ ≫ τ.f ≫ Q.G.ι := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q ex p _ y y₀ t c tm hbig
  have hin := GlobalTheory.T.testModel_maps_into_openPart hL o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hbig
  have hrange : Set.range (tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) ⊆ Set.range Q.G.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hin (Set.mem_univ x)
  let f' : t.u.G.left ⟶ Q.G.toScheme := IsOpenImmersion.lift Q.G.ι _ hrange
  have hf' : f' ≫ Q.G.ι = tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨-, hloc, hinj, -⟩ := GlobalTheory.T.testField_finite_over_padic o Ω S ρ p y₀ t.u
  obtain ⟨-, -, hsm, -, hsplit⟩ := GlobalTheory.T.uniformisedTest_dimensions_and_split_fibre hL o Ω S ρ p y₀ t.u
  have hgen := t.u.U.gen_hom
  have g1 : IsGrpPullback ((Over.pullback (jK t.u.V)).obj t.u.G) ρ.P.A (c.yK ≫ Q.u₀)
      (tm.φ ≫ pullback.fst ρ.P.A.hom Q.u₀) :=
    ((isGrpPullback_of_iso t.u.U.gen).comp t.u.cart).congr
      ((Category.id_comp _).trans c.yK_u.symm) tm.φ_fst.symm
  have g2 : IsGrpPullback ((Over.pullback (jK t.u.V)).obj t.u.G) ((Over.pullback Q.u₀).obj ρ.P.A) c.yK tm.φ :=
    (isGrpPullback_pullback ρ.P.A Q.u₀).cancel g1 tm.φ_snd
  let τ : ex.core.Test y :=
    { V := t.u.V
      complete := t.u.complete
      j := t.u.j
      j_inj := hinj
      j_loc := hloc
      y₀ := c.yV
      fac := c.fac
      H := t.u.G
      smooth := hsm
      sep := t.u.U.separated
      qc := t.u.semi.quasiCompact
      split := hsplit
      f := f'
      f_over := by
        change f' ≫ Q.G.ι ≫ Q.P.hom = _
        rw [← Category.assoc, hf', Category.assoc]
        exact tm.f_over
      yK := c.yK
      yK_fac := c.yK_fac
      φ := tm.φ
      φ_cart := g2
      φ_f := by
        change tm.φ ≫ ex.a = pullback.fst t.u.G.hom (jK t.u.V) ≫ f'
        rw [← cancel_mono Q.G.ι, Category.assoc, ex.a_eq, Category.assoc, hf']
        exact tm.φ_f
      imm := GlobalTheory.T.isClosedImmersion_testSpecialFibre_openPart hL o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hbig f' hf'
      lift := by
        intro b hb
        change Sp (OO p) ⟶ Q.G.toScheme at b
        obtain ⟨c', h1, h2⟩ := GlobalTheory.T.exists_lift_integralPoint_closure_testModel hL o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hbig (b ≫ Q.G.ι)
          ((Category.assoc _ _ _).trans hb) (by
            intro x _
            change (b ≫ Q.G.ι) x ∈ Q.G
            rw [Scheme.Hom.comp_apply]
            exact (b x).2)
        refine ⟨c', h1, ?_⟩
        change c' ≫ f' = b
        rw [← cancel_mono Q.G.ι, Category.assoc, hf']
        exact h2 }
  have hc : IsPullback t.mod.r t.mod.Φ.G.hom t.u.G.hom (rPt p ≫ spMap t.u.j) := t.mod.cart.1
  refine ⟨τ, hc.isoPullback.symm, hc.isoPullback_inv_snd, ?_⟩
  change hc.isoPullback.inv ≫ _ = pullback.fst t.u.G.hom (rPt p ≫ spMap t.u.j) ≫ f' ≫ Q.G.ι
  rw [hf', ← Category.assoc, hc.isoPullback_inv_fst]

end GlobalTheory.ZH
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationTestOfGeometricTestStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.exists_uniformisationTest_of_geometricTest : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext) (p : ℕ) [Fact p.Prime] (y : Sp (GlobalTheory.ZJ.OO p) ⟶ ex.core.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ∃ (τ : ex.core.Test y) (e : pullback τ.H.hom (GlobalTheory.ZJ.rPt p ≫ spMap τ.j) ≅ t.mod.Φ.G.left), e.hom ≫ t.mod.Φ.G.hom = pullback.snd _ _ ∧ e.hom ≫ t.mod.r ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = pullback.fst _ _ ≫ τ.f ≫ Q.G.ι := by
  first | exact @GlobalTheory.ZH.Clos.exists_core_test_of_geoTest | exact GlobalTheory.ZH.Clos.exists_core_test_of_geoTest | (intros; apply GlobalTheory.ZH.Clos.exists_core_test_of_geoTest <;> assumption)
end
end
