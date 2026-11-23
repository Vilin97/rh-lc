module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueExpansionSectionAdmissibleBase
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermDvdOfSectionExpansionDvdClosedFibreStatement
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CstDvdOfCstMulEqZero
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsAtSecIsMul
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSectionDvdEverywhereSmoothConnectedFibStatement
public import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsAtSecIsMul
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EgaHolds
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseMulSectionOfGermDvdFlatDomain

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_secIsMul_of_germ_dvd : ∀ (R : Type) [CommRing R] [IsDomain R] (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R)), Flat p → ∀ (L : LB X) (s : LB.Sec L) (q : R), q ≠ 0 → (∀ (x : X) j, x ∈ L.U j → ∃ t, gs (𝟙 X) x (L.U j) (s.f j) = cst p x q * t) → ∃ t : LB.Sec L, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p q s t := by
  intro R _ _ X p hp L s q hq h
  haveI : Flat (X := X) (Y := Sp R) p := hp
  have loc : ∀ j, ∃ g : Γ(X, L.U j), s.f j = constFn p (L.U j) q * g := fun j =>
    exists_div p hq (L.U j) (s.f j) (fun x hx => h x j hx)
  choose t ht using loc
  have hg : ∀ j (x : X), x ∈ L.U j → gs (𝟙 X) x (L.U j) (s.f j) = cst p x q * gs (𝟙 X) x (L.U j) (t j) := by
    intro j x hx
    rw [ht j, gs_mul _ _ _ hx, gs_constFn p (L.U j) (𝟙 X) x hx, Category.id_comp]
  refine ⟨⟨t, fun i j => ?_⟩, fun j => ?_⟩
  · refine fn_ext fun x hx => ?_
    have e := congrArg (gs (𝟙 X) x (L.U i ⊓ L.U j)) (s.compat i j)
    rw [gs_mul _ _ _ hx, gs_res _ _ _ hx, gs_res _ _ _ hx] at e ⊢
    rw [hg i x hx.1, hg j x hx.2, mul_left_comm] at e
    exact cst_regular p x hq e
  · exact ht j

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseMulSectionOfGermDvdFlatDomainStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_baseMul_section_of_germ_dvd_flat_domain : ∀ (R : Type) [CommRing R] [IsDomain R] (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R)), Flat p → ∀ (L : LB X) (s : LB.Sec L) (q : R), q ≠ 0 → (∀ (x : X) j, x ∈ L.U j → ∃ t, gs (𝟙 X) x (L.U j) (s.f j) = cst p x q * t) → ∃ t : LB.Sec L, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p q s t := by
  first | exact @GlobalTheory.Mum.exists_secIsMul_of_germ_dvd | exact GlobalTheory.Mum.exists_secIsMul_of_germ_dvd | (intros; apply GlobalTheory.Mum.exists_secIsMul_of_germ_dvd <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSectionBaseMulCancelFlatDomain

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem secIsMul_cancel : ∀ (R : Type) [CommRing R] [IsDomain R] (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R)), Flat p → ∀ (L : LB X) (q : R), q ≠ 0 → ∀ s t t' : LB.Sec L, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p q s t → ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p q s t' → t = t' := by
  intro R _ _ X p hp L q hq s t t' h h'
  haveI := hp
  have key : ∀ j, t.f j = t'.f j := by
    intro j
    refine fn_ext fun x hx => ?_
    have e1 := GlobalTheory.secIsMul_gs h (𝟙 X) x j hx
    have e2 := GlobalTheory.secIsMul_gs h' (𝟙 X) x j hx
    rw [Category.id_comp] at e1 e2
    have h0 : cst p x q * (gs (𝟙 X) x (L.U j) (t.f j) - gs (𝟙 X) x (L.U j) (t'.f j)) = 0 := by
      rw [mul_sub, ← e1, ← e2, sub_self]
    obtain ⟨u, hu⟩ := GlobalTheory.cst_dvd_of_cst_mul_eq_zero p x (a := q) (b := 0)
      (fun c hc => by
        rcases mul_eq_zero.1 hc with h1 | h1
        · exact absurd h1 hq
        · rw [h1]) h0
    have hz : cst p x (0 : R) = 0 := by
      rw [cst, map_zero, gs_eq _ _ ⊤ trivial, map_zero, map_zero]
    rw [hz, zero_mul, sub_eq_zero] at hu
    exact hu
  cases t; cases t'
  congr 1
  exact funext key

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSectionBaseMulCancelFlatDomainStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.lineBundleSection_baseMul_cancel_flat_domain : ∀ (R : Type) [CommRing R] [IsDomain R] (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R)), Flat p → ∀ (L : LB X) (q : R), q ≠ 0 → ∀ s t t' : LB.Sec L, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p q s t → ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p q s t' → t = t' := by
  first | exact @GlobalTheory.Mum.secIsMul_cancel | exact GlobalTheory.Mum.secIsMul_cancel | (intros; apply GlobalTheory.Mum.secIsMul_cancel <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionExpansionScaleBaseElement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.UU.expT_scale : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU I D A G) (k : ℕ) (q : R) (σ τ : U.SecGT (𝟙_ _) k) (f g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) k α), ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ G).hom q σ τ → (∀ α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q (f α) (g α)) → U.ExpT (𝟙_ _) k τ g → U.ExpT (𝟙_ _) k σ f := by
  intro R _ _ I D A G _ _ U k q σ τ f g hσ hf hE e
  obtain ⟨s, hs⟩ := hE e
  refine ⟨s, fun Z x rG rB h1 h2 h3 z JG J hG hB => ?_⟩
  obtain ⟨H1, H2⟩ := hs Z x rG rB h1 h2 h3 z JG J hG hB
  have hc : cst (rB ≫ (𝟙_ _ ⊗ D.P.A).hom) z q = cst (rG ≫ (𝟙_ _ ⊗ G).hom) z q := by
    rw [← Over.w (fst (𝟙_ (Over (Spec (CommRingCat.of R)))) D.P.A), ← Over.w (fst (𝟙_ (Over (Spec (CommRingCat.of R)))) G),
      ← Category.assoc, ← Category.assoc, h3]
  have hF : ∀ α, sval (f α) rB z J = cst (rG ≫ (𝟙_ _ ⊗ G).hom) z q * sval (g α) rB z J := fun α => by
    rw [← hc]
    exact GlobalTheory.secIsMul_gs (hf α) rB z _ (hB.mem _ _)
  have hS : sval σ rG z JG = cst (rG ≫ (𝟙_ _ ⊗ G).hom) z q * sval τ rG z JG :=
    GlobalTheory.secIsMul_gs hσ rG z _ (hG.mem _ _)
  refine ⟨fun α hα => by rw [hF, H1 α hα, mul_zero], ?_⟩
  rw [hS, mul_left_comm, H2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun α _ => by rw [hF, _root_.mul_assoc]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionExpansionScaleBaseElementStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.sectionExpansion_scale_base_element : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU I D A G) (k : ℕ) (q : R) (σ τ : U.SecGT (𝟙_ _) k) (f g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) k α), ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ G).hom q σ τ → (∀ α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q (f α) (g α)) → U.ExpT (𝟙_ _) k τ g → U.ExpT (𝟙_ _) k σ f := by
  first | exact @GlobalTheory.UU.expT_scale | exact GlobalTheory.UU.expT_scale | (intros; apply GlobalTheory.UU.expT_scale <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionQuotientOfExpansionDvd

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.SecDiv

theorem resTop_map {Y : Scheme.{0}} {V W : Y.Opens} (h : W ≤ V) (c : Γ(Y, ⊤)) :
    (Y.presheaf.map (homOfLE h).op).hom (ReciprocityTheory.ChartRestriction.G.Out.resTop V c) = ReciprocityTheory.ChartRestriction.G.Out.resTop W c := by
  unfold ReciprocityTheory.ChartRestriction.G.Out.resTop
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem exists_secIsMul {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) {L : LB Y}
    (a : R) (τ : LB.Sec L) : ∃ σ : LB.Sec L, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p a σ τ := by
  unfold ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul
  refine ⟨⟨fun j => ReciprocityTheory.ChartRestriction.G.Out.resTop (L.U j) (scal p a) * τ.f j, fun i j => ?_⟩, fun j => rfl⟩
  simp only [map_mul, resTop_map]
  rw [τ.2 i j]
  ring

theorem exists_expT_of_dvd : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G) (σ : U.SecGT (𝟙_ _) 1) (f g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) 1 α) (q : R), q ≠ 0 → U.ExpT (𝟙_ _) 1 σ f → (∀ α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q (f α) (g α)) → ∃ τ : U.SecGT (𝟙_ _) 1, U.ExpT (𝟙_ _) 1 τ g := by
  intro R _ _ _ hB D A G _ _ U σ f g q hq hσ hfg
  have hB' : AdmBase R (maximalIdeal R) ∧ CharZero R := hB
  have h1 : IsNoetherianRing R ∧ IsDomain R ∧ IsIntegrallyClosed R ∧ IsAdicComplete (maximalIdeal R) R := hB'.1
  obtain ⟨hN, -, hIC, hC⟩ := h1
  haveI := hN
  haveI := hIC
  have hs := U.semi
  haveI := hs.smooth
  haveI := hs.geomConnected
  haveI : IsIso (λ_ G).hom.left := inferInstanceAs (IsIso ((Over.forget _).mapIso (λ_ G)).hom)
  have hSm : Smooth (𝟙_ (Over (Sp R)) ⊗ G).hom := by
    rw [← Over.w (λ_ G).hom]
    infer_instance
  have hGC : GeometricallyConnected (𝟙_ (Over (Sp R)) ⊗ G).hom := by
    have hsq : IsPullback (λ_ G).hom.left (𝟙_ (Over (Sp R)) ⊗ G).hom G.hom (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [Over.w, Category.comp_id]⟩
    exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) hsq inferInstance
  have he : (η[G].left ≫ (λ_ G).inv.left) ≫ (𝟙_ (Over (Sp R)) ⊗ G).hom = 𝟙 _ := by
    simp only [Category.assoc, Over.w]
    rfl
  have hLB : (LB.LinComb U.P.L.L (K := Fin 1) (fun _ : Fin 1 => (snd (𝟙_ (Over (Sp R))) G).left)
      (fun _ => ((1 : ℕ) : ℤ))).IsLB := by
    first
    | exact ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ U.P.L.isLB _ _
    | exact ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ _ _
  have hloc := GlobalTheory.T.germ_dvd_of_sectionExpansion_dvd_closedFibre R hB D A G U σ f g q hσ hfg
  have hall := GlobalTheory.T.lineBundle_section_dvd_everywhere_smooth_connected_fibres R _ (𝟙_ (Over (Sp R)) ⊗ G).hom hSm hGC _ he _ hLB σ q hq hloc
  have hflat : Flat (𝟙_ (Over (Sp R)) ⊗ G).hom := inferInstance
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_baseMul_section_of_germ_dvd_flat_domain R _ (𝟙_ (Over (Sp R)) ⊗ G).hom hflat _ σ q hq hall
  have hEga : GlobalTheory.LN.AlgSt ∧ GlobalTheory.LN.MorAlgSt ∧ GlobalTheory.LN.SecAlgSt ∧ GlobalTheory.LN.PicardZeroDegenerationCondition := GlobalTheory.LN.ega_holds
  obtain ⟨h, hh⟩ := GlobalTheory.CompleteBaseExpansion.exists_expT hEga.2.2.1 hC U 1 τ
  choose f' hf' using fun α => exists_secIsMul (𝟙_ (Over (Sp R)) ⊗ D.P.A).hom q (h α)
  have hσf' : U.ExpT (𝟙_ _) 1 σ f' := GlobalTheory.T.sectionExpansion_scale_base_element R (maximalIdeal R) D A G U 1 q σ τ f' h hτ hf' hh
  have hjac : maximalIdeal R ≤ Ideal.jacobson ⊥ := (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  have hff' : f' = f := GlobalTheory.CompleteBaseExpansion.expT_unique hjac U 1 σ f' f hσf' hσ
  have hflatD : Flat (𝟙_ (Over (Sp R)) ⊗ D.P.A).hom := by
    haveI : IsIso (λ_ D.P.A).hom.left := inferInstanceAs (IsIso ((Over.forget _).mapIso (λ_ D.P.A)).hom)
    haveI : Smooth D.P.A.hom := D.P.isAb.smooth
    rw [← Over.w (λ_ D.P.A).hom]
    infer_instance
  have hhg : h = g := by
    funext α
    have hfa := hf' α
    rw [hff'] at hfa
    exact GlobalTheory.T.lineBundleSection_baseMul_cancel_flat_domain R _ _ hflatD _ q hq (f α) (h α) (g α) hfa (hfg α)
  refine ⟨τ, ?_⟩
  rw [← hhg]
  exact hh

end GlobalTheory.SecDiv
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionQuotientOfExpansionDvdStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_section_quotient_of_expansion_dvd : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G) (σ : U.SecGT (𝟙_ _) 1) (f g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) 1 α) (q : R), q ≠ 0 → U.ExpT (𝟙_ _) 1 σ f → (∀ α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q (f α) (g α)) → ∃ τ : U.SecGT (𝟙_ _) 1, U.ExpT (𝟙_ _) 1 τ g := by
  first | exact @GlobalTheory.SecDiv.exists_expT_of_dvd | exact GlobalTheory.SecDiv.exists_expT_of_dvd | (intros; apply GlobalTheory.SecDiv.exists_expT_of_dvd <;> assumption)
end
end
