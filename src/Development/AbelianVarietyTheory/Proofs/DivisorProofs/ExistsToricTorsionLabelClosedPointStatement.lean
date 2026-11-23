module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteLocalBaseAtClosedPointGroupImports
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastTail
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFactorClassicalPointOfLargeTest
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointCompletionPositiveResidueChar
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfGenericAbelianOfClosedIsGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantOfGeneric

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.Poinc.LabIndex

theorem pow_left_congr {S X : Scheme.{0}} {G : Over S} [GrpObj G] {a b : X ⟶ S} (h : a = b)
    (x : Over.mk a ⟶ G) (x' : Over.mk b ⟶ G) (hx : x.left = x'.left) (n : ℕ) :
    (x ^ n).left = (x' ^ n).left := by
  subst h
  rw [Over.OverMorphism.ext hx]

theorem eq_of_comp_fst {P X Y Z T : Scheme.{0}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) [Mono g] {a b : T ⟶ P} (e : a ≫ fst = b ≫ fst) : a = b :=
  h.hom_ext e ((cancel_mono g).1 (by rw [Category.assoc, Category.assoc, ← h.w, ← Category.assoc, e, Category.assoc]))

theorem isDominant_of_generic {R : Type} [CommRing R] [IsDomain R] (W : (Sp R).Opens) {K : Type} [Field K]
    (eg : Sp K ⟶ W.toScheme) (heg : ∀ w, W.ι (eg w) = genericPoint (Sp R)) : IsDominant eg := by
  refine ⟨fun w => ?_⟩
  let w0 : Sp K := genericPoint (Sp K)
  have h1 : eg w0 ⤳ w := by
    rw [← W.ι.isOpenEmbedding.isInducing.specializes_iff, heg w0]
    exact genericPoint_specializes _
  exact closure_mono (Set.singleton_subset_iff.2 (Set.mem_range_self w0)) (specializes_iff_mem_closure.1 h1)

theorem spMap_generic (R : Type) [CommRing R] [IsDomain R] (w : Sp (AlgebraicClosure (FractionRing R))) :
    spMap ((algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))).comp (algebraMap R (FractionRing R))) w =
      genericPoint (Sp R) := by
  have hw : w = genericPoint (Sp (AlgebraicClosure (FractionRing R))) := Subsingleton.elim _ _
  subst hw
  rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  show Ideal.comap ((algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))).comp
    (algebraMap R (FractionRing R))) ⊥ = ⊥
  exact Ideal.comap_bot_of_injective _
    ((algebraMap (FractionRing R) _).injective.comp (IsFractionRing.injective R (FractionRing R)))

end GlobalTheory.Poinc.LabIndex

namespace GlobalTheory.Poinc.LabIndex

theorem one_left_congr {S X : Scheme.{0}} {G : Over S} [GrpObj G] {a b : X ⟶ S} (h : a = b) :
    (1 : Over.mk a ⟶ G).left = (1 : Over.mk b ⟶ G).left := by
  subst h
  rfl

theorem torsion_section_label : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∀ s : 𝟙_ (Over (Sp R)) ⟶ G, s ^ (S.r * S.N) = 1 → ∃ b : S.Gam, ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ → ∀ t : Sp (PadicAlgCl p) ⟶ pullback ρ.P.A.hom FinalForm.u₀, t ≫ FinalForm.φ = spMap ((OO p).subtype.comp ev) ≫ s.left ≫ gm → t ≫ pullback.fst _ _ = spMap y₀ ≫ (ρ.pt b).left := by
  intro o' Ω _ _ _ _ S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R _ _ _ j hBase hcpl G _ _ gm hgm D A U hLB hpsi s hs
  set ξ : Sp R ⟶ M.Z := spMap j ≫ M.Z.fromSpecStalk x with hξdef
  let W : (Sp R).Opens := ξ ⁻¹ᵁ U₀
  have hrW : Set.range (W.ι ≫ ξ) ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact w.2
  let w₀ : W.toScheme ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι (W.ι ≫ ξ) hrW
  have hw₀ : w₀ ≫ U₀.ι = W.ι ≫ ξ := IsOpenImmersion.lift_fac _ _ _
  have hsG : s.left ≫ G.hom = 𝟙 _ := Over.w s
  have hσw : (W.ι ≫ s.left ≫ gm) ≫ FinalForm.G.hom = w₀ ≫ U₀.ι := by
    rw [hw₀, Category.assoc, Category.assoc, hgm.1.w, ← Category.assoc s.left, hsG, Category.id_comp]
  let σ : W.toScheme ⟶ pullback ρ.P.A.hom FinalForm.u₀ := FinalForm.cart.1.lift _ _ hσw
  have hσ1 : σ ≫ FinalForm.φ = W.ι ≫ s.left ≫ gm := FinalForm.cart.1.lift_fst _ _ _
  have hσ2 : σ ≫ pullback.snd ρ.P.A.hom FinalForm.u₀ = w₀ := FinalForm.cart.1.lift_snd _ _ _
  have key : (W : Set (Sp R)).Nonempty →
      ∃ b : S.Gam, σ ≫ pullback.fst ρ.P.A.hom FinalForm.u₀ = (w₀ ≫ FinalForm.u₀) ≫ (ρ.pt b).left := by
    intro hWne
    let K := AlgebraicClosure (FractionRing R)
    let e0 : Sp K ⟶ Sp R := spMap ((algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R)))
    have he0 : ∀ w, e0 w = genericPoint (Sp R) := spMap_generic R
    have hgW : genericPoint (Sp R) ∈ W := by
      obtain ⟨w, hw⟩ := hWne
      exact (genericPoint_specializes w).mem_open W.isOpen hw
    have hr : Set.range e0 ⊆ Set.range W.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨w, rfl⟩
      rw [he0]
      exact hgW
    let eg : Sp K ⟶ W.toScheme := IsOpenImmersion.lift W.ι e0 hr
    have heg : eg ≫ W.ι = e0 := IsOpenImmersion.lift_fac _ _ _
    haveI : IsDominant eg := isDominant_of_generic W eg (fun w => by rw [← Scheme.Hom.comp_apply, heg, he0])
    haveI : IsSeparated ρ.P.A.hom := by haveI := ρ.P.isAb.proper; infer_instance
    let T : Over (Sp R) := Over.mk e0
    have htu : (toUnit T).left = e0 := (Category.comp_id _).symm.trans (Over.w (toUnit T))
    let x1 : T ⟶ G := toUnit T ≫ s
    have hx1 : x1 ^ (S.r * S.N) = 1 := by
      show ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom (toUnit T) s ^ (S.r * S.N) = 1
      rw [← map_pow, hs, map_one]
    let x2 := pushHom hgm T x1
    have hx2 : x2 ^ (S.r * S.N) = 1 := by
      show pushHom hgm T x1 ^ (S.r * S.N) = 1
      rw [← map_pow, hx1, map_one]
    let T' : Over U₀.toScheme := Over.mk (eg ≫ w₀)
    let x3 : T' ⟶ (Over.pullback FinalForm.u₀).obj ρ.P.A := Over.homMk (eg ≫ σ) (by
      show (eg ≫ σ) ≫ pullback.snd _ _ = eg ≫ w₀
      rw [Category.assoc, hσ2])
    have hbase : T'.hom ≫ U₀.ι = T.hom ≫ ξ := by
      show (eg ≫ w₀) ≫ U₀.ι = e0 ≫ ξ
      rw [Category.assoc, hw₀, ← Category.assoc, heg]
    have hx3 : x3 ^ (S.r * S.N) = 1 := by
      apply Over.OverMorphism.ext
      apply eq_of_comp_fst FinalForm.cart.1
      have a1 : ((pushHom FinalForm.cart T') (x3 ^ (S.r * S.N))).left = ((pushHom FinalForm.cart T' x3) ^ (S.r * S.N)).left := by
        rw [map_pow]
      have a2 : ((pushHom FinalForm.cart T') 1).left = (1 : Over.mk (T'.hom ≫ U₀.ι) ⟶ FinalForm.G).left := by
        rw [map_one]
      have a3 := pow_left_congr hbase (pushHom FinalForm.cart T' x3) x2 (by
        show (eg ≫ σ) ≫ FinalForm.φ = (toUnit T ≫ s).left ≫ gm
        rw [Over.comp_left, htu, Category.assoc, hσ1, ← Category.assoc eg, heg]
        simp only [Category.assoc]) (S.r * S.N)
      have a4 := one_left_congr (G := FinalForm.G) hbase
      refine a1.trans (a3.trans ?_)
      rw [hx2, ← a4, ← a2]
      rfl
    let x4 := pushHom (isGrpPullback_pullback ρ.P.A FinalForm.u₀) T' x3
    have hx4 : x4 ^ (S.r * S.N) = 1 := by
      show pushHom (isGrpPullback_pullback ρ.P.A FinalForm.u₀) T' x3 ^ (S.r * S.N) = 1
      rw [← map_pow, hx3, map_one]
    obtain ⟨b, hb, -⟩ := ρ.pt_bij K (T'.hom ≫ FinalForm.u₀) x4 hx4
    refine ⟨b, ext_of_isDominant_of_isSeparated ρ.P.A.hom ?_ eg ?_⟩
    · have e1 : (ρ.pt b).left ≫ ρ.P.A.hom = 𝟙 _ := Over.w (ρ.pt b)
      rw [Category.assoc, pullback.condition, ← Category.assoc, hσ2, Category.assoc, e1]
      exact (Category.comp_id _).symm
    · have e2 := congrArg (fun z => z.left) hb
      simp only [Over.comp_left, Over.homMk_left] at e2
      rw [← Category.assoc, ← Category.assoc]
      exact (e2.trans rfl).symm
  by_cases hWne : (W : Set (Sp R)).Nonempty
  · obtain ⟨b, hb⟩ := key hWne
    refine ⟨b, fun p _ y ev hCen hev y₀ hAt t ht => ?_⟩
    let c : Sp (PadicAlgCl p) ⟶ Sp R := spMap ((OO p).subtype.comp ev)
    have hc : c ≫ ξ = gPt p ≫ y := by
      rw [← hev]
      simp only [c, gPt, spMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hcW : Set.range c ⊆ Set.range W.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨w, rfl⟩
      show ξ (c w) ∈ U₀
      rw [← Scheme.Hom.comp_apply, hc]
      exact hCen.2 ⟨w, rfl⟩
    let c' : Sp (PadicAlgCl p) ⟶ W.toScheme := IsOpenImmersion.lift W.ι c hcW
    have hc' : c' ≫ W.ι = c := IsOpenImmersion.lift_fac _ _ _
    have htc : t = c' ≫ σ := eq_of_comp_fst FinalForm.cart.1 (by
      rw [ht, Category.assoc, hσ1, ← Category.assoc c', hc'])
    have hq : (c' ≫ w₀) ≫ U₀.ι = gPt p ≫ y := by
      rw [Category.assoc, hw₀, ← Category.assoc, hc', hc]
    have hu : (c' ≫ w₀) ≫ FinalForm.u₀ = spMap y₀ := by
      rw [← Spec.map_preimage ((c' ≫ w₀) ≫ FinalForm.u₀)]
      congr 1
      ext a
      rw [GlobalTheory.ZH.preimage_comp_eq_val M U₀ hAdm.1.ne S.R FinalForm.u₀ FinalForm.u₀_gen, hq, ← hAt a]
      rfl
    rw [htc, Category.assoc, hb, ← Category.assoc, ← Category.assoc, hu]
  · refine ⟨0, fun p _ y ev hCen hev y₀ hAt t ht => absurd ?_ hWne⟩
    let c : Sp (PadicAlgCl p) ⟶ Sp R := spMap ((OO p).subtype.comp ev)
    have hc : c ≫ ξ = gPt p ≫ y := by
      rw [← hev]
      simp only [c, gPt, spMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    refine ⟨c (genericPoint _), ?_⟩
    show ξ (c (genericPoint _)) ∈ U₀
    rw [← Scheme.Hom.comp_apply, hc]
    exact hCen.2 ⟨_, rfl⟩

end GlobalTheory.Poinc.LabIndex
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValGPtOfStalk

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.Poinc.TestAtPt

theorem val_gPt_of_stalk : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (x : M.Z) (R : Type) [CommRing R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), IsLocalHom j → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ c : M.O x, ((ev (j ((M.stalkEquiv x).symm c)) : OO p) : PadicAlgCl p) = M.val (gPt p ≫ y) (c : Ω) := by
  intro o Ω _ _ _ M x R _ _ j _ p _ y ev hy c
  have hsp : ∀ w, (spMap j ≫ M.Z.fromSpecStalk x) w ⤳ x := fun w => by
    have : M.Z.fromSpecStalk x (spMap j w) ∈ Set.range (M.Z.fromSpecStalk x) := ⟨_, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this
  obtain ⟨U, hx, f, hf⟩ := M.Z.presheaf.germ_exist ((M.stalkEquiv x).symm c)
  have hc : c = ⟨valF M.pt U f, RatModel.valF_mem_O hx f⟩ := by
    rw [← RatModel.stalkEquiv_germ hx, hf, RingEquiv.apply_symm_apply]
  have hU : ⊤ ≤ (spMap j ≫ M.Z.fromSpecStalk x) ⁻¹ᵁ U := fun w _ => (hsp w).mem_open U.isOpen hx
  have hU0 : ⊤ ≤ M.Z.fromSpecStalk x ⁻¹ᵁ U := fun w _ => by
    have : M.Z.fromSpecStalk x w ∈ Set.range (M.Z.fromSpecStalk x) := ⟨_, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this.mem_open U.isOpen hx
  have hg : gPt p ≫ y = spMap ((OO p).subtype.comp ev) ≫ (spMap j ≫ M.Z.fromSpecStalk x) := by
    rw [← hy, ← Category.assoc]
    congr 1
    rw [gPt, spMap, spMap, spMap, ← Spec.map_comp]
    rfl
  have hU' : ⊤ ≤ (gPt p ≫ y) ⁻¹ᵁ U := by
    rw [hg]; exact fun w _ => hU (x := spMap ((OO p).subtype.comp ev) w) trivial
  rw [RatModel.val_eq ((top_le_preimage_iff _ _).1 hU') (f := f) (hc ▸ rfl), GlobalTheory.Points.valF_eq_valR, hg,
    GlobalTheory.Points.valR_spMap_comp _ _ U hU]
  have e1 : valR (spMap j ≫ M.Z.fromSpecStalk x) U f = j (valR (A := M.Z.presheaf.stalk x) (M.Z.fromSpecStalk x) U f) :=
    GlobalTheory.Points.valR_spMap_comp (C := M.Z.presheaf.stalk x) j (M.Z.fromSpecStalk x) U hU0 f
  have e2 : valR (A := M.Z.presheaf.stalk x) (M.Z.fromSpecStalk x) U f = M.Z.presheaf.germ U x hx f := by
    have eA : (M.Z.fromSpecStalk x).appLE U ⊤ hU0 =
        M.Z.presheaf.germ U x hx ≫ (Scheme.ΓSpecIso (M.Z.presheaf.stalk x)).inv := by
      rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
      simp only [Category.assoc, ← Functor.map_comp]
      have e : ((homOfLE le_top).op ≫ (homOfLE hU0).op :
          Opposite.op (⊤ : (Spec (M.Z.presheaf.stalk x)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ := rfl
      rw [e, CategoryTheory.Functor.map_id, Category.comp_id]
    unfold valR
    erw [dite_eq_left hU0, eA]
    simp only [CommRingCat.comp_apply]
    erw [Iso.inv_hom_id_apply]
    rfl
  rw [e1]
  exact (congrArg (fun t => ((OO p).subtype.comp ev) (j t)) (e2.trans hf)).symm

end GlobalTheory.Poinc.TestAtPt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToricTorsionLabelClosedPoint

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.Poinc.ToricLabel

theorem exists_label : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∀ lam : D.toPre.X →+ ZMod (S.r * S.N), ∃ b : S.Gam, ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ → ∀ (u : ρ.UTest p y₀) (ε : D.toPre.X ≃+ u.D.toPre.X), GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev u ε → ∀ (τ' : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ), (∀ χ, ((τ' (Multiplicative.ofAdd (ε χ)) : (PadicAlgCl p)ˣ) : PadicAlgCl p) = y₀ (algebraMap o' S.R S.ζ) ^ (S.r * S.N * (lam χ).val)) → ∀ (q : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), q.y = 0 → GlobalTheory.UT.IsTor τ' q.g → QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) q x' → x'.left ≫ u.φ = spMap y₀ ≫ (ρ.pt b).left := by
  intro o' Ω _ _ _ _ S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R _ _ _ j hBase hCpl G _ _ gm hpb D A U hLB hPsi lam
  have hj : IsLocalHom j := GlobalTheory.UPoinc.ClosedPt.isLocalHom_of_isCpl hCpl
  have hk0 : S.r * S.N ≠ 0 := Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)
  haveI : NeZero (S.r * S.N) := ⟨hk0⟩
  set ζR : R := j ((M.stalkEquiv x).symm (algebraMap o' (M.O x) S.ζ)) with hζR
  have hζpow : ζR ^ ((S.r * S.N) ^ 2) = 1 := by
    rw [hζR, ← map_pow, ← map_pow, ← map_pow, S.prim.pow_eq_one, map_one, map_one, map_one]
  let u0 : Rˣ := Units.ofPowEqOne ζR ((S.r * S.N) ^ 2) hζpow (pow_ne_zero 2 hk0)
  have hu0 : ((u0 : Rˣ) : R) = ζR := Units.val_ofPowEqOne _ _ _ _
  let w : Rˣ := u0 ^ (S.r * S.N)
  have hw : w ^ (S.r * S.N) = 1 := by
    rw [← pow_mul, ← sq]; ext; rw [Units.val_pow_eq_pow_val, hu0, hζpow, Units.val_one]
  let τ : Multiplicative D.toPre.X →* Rˣ :=
    { toFun := fun χ => w ^ (lam (Multiplicative.toAdd χ)).val
      map_one' := by simp
      map_mul' := fun a b => by
        rw [toAdd_mul, map_add (f := _), ZMod.val_add, ← pow_eq_pow_mod _ hw, pow_add] }
  have hτ : τ ^ (S.r * S.N) = 1 := by
    refine MonoidHom.ext fun χ => ?_
    rw [MonoidHom.pow_apply, MonoidHom.one_apply]
    show (w ^ (lam (Multiplicative.toAdd χ)).val) ^ (S.r * S.N) = 1
    rw [← pow_mul, mul_comm, pow_mul, hw, one_pow]
  have hsemi : IsSemiAbelian G := by
    obtain ⟨e, he, -⟩ := grpPullback_iso hpb (isGrpPullback_pullback FinalForm.G _)
    haveI := he
    exact GlobalTheory.isSemiAbelian_of_grpIso e (IsSemiAbelian.pullback _ FinalForm.G FinalForm.semi)
  obtain ⟨s, hs, hspec⟩ := GlobalTheory.ToricTorsionSpec.main R hBase G hsemi D A U (S.r * S.N) (Nat.one_le_iff_ne_zero.2 hk0) τ hτ
  obtain ⟨b, hb⟩ := GlobalTheory.Poinc.LabIndex.torsion_section_label o' Ω S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R j hBase hCpl G gm hpb D A U hLB hPsi s hs
  refine ⟨b, ?_⟩
  intro p _ y ev hCen hy y₀ hAt u ε hBC τ' hτ' q x' hq hTor hQk
  obtain ⟨ev₀, hloc, hD, bc, hmon, hpull, hxe, hev, t, ht1, ht2⟩ := hBC
  haveI : CharZero u.V :=
    RingHom.charZero ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V)))
  have hring : (algebraMap (FractionRing u.V) (PadicAlgCl p)).comp ((algebraMap u.V (FractionRing u.V)).comp ev₀) =
      (OO p).subtype.comp ev := RingHom.ext hev
  have hζ : ((ev ζR : OO p) : PadicAlgCl p) = y₀ (algebraMap o' S.R S.ζ) := by
    rw [hζR, GlobalTheory.Poinc.TestAtPt.val_gPt_of_stalk o' Ω M x R j hj p y ev hy, hAt]
    rfl
  have hchar : ∀ χ', ((τ' χ' : (PadicAlgCl p)ˣ) : PadicAlgCl p) = algebraMap (FractionRing u.V) (PadicAlgCl p)
      (algebraMap u.V (FractionRing u.V) (ev₀ ((τ (Multiplicative.ofAdd (hD.xe (Multiplicative.toAdd χ'))) : Rˣ) : R))) := by
    intro χ'
    obtain ⟨χ, hχ⟩ := ε.surjective (Multiplicative.toAdd χ')
    have e1 : χ' = Multiplicative.ofAdd (ε χ) := by rw [hχ]; rfl
    subst e1
    rw [hτ' χ, hev]
    simp only [toAdd_ofAdd, hxe]
    show _ = ((ev (((w ^ (lam χ).val : Rˣ) : R)) : OO p) : PadicAlgCl p)
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hu0, map_pow, map_pow, SubmonoidClass.coe_pow,
      SubmonoidClass.coe_pow, hζ, ← pow_mul]
  have key := hspec u.V u.complete ev₀ hloc u.G bc hmon u.D u.A hD u.U hpull (PadicAlgCl p) τ' hchar q x' hq hTor hQk
  have h2 := hb p y ev hCen hy y₀ hAt (x'.left ≫ t) (by
    rw [Category.assoc, ht2, ← hring]
    simpa only [Category.assoc] using congrArg (· ≫ gm) key)
  rw [Category.assoc, ht1] at h2
  exact h2

end GlobalTheory.Poinc.ToricLabel
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToricTorsionLabelClosedPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.exists_toricTorsion_label_closed_point : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∀ lam : D.toPre.X →+ ZMod (S.r * S.N), ∃ b : S.Gam, ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ → ∀ (u : ρ.UTest p y₀) (ε : D.toPre.X ≃+ u.D.toPre.X), GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev u ε → ∀ (τ' : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ), (∀ χ, ((τ' (Multiplicative.ofAdd (ε χ)) : (PadicAlgCl p)ˣ) : PadicAlgCl p) = y₀ (algebraMap o' S.R S.ζ) ^ (S.r * S.N * (lam χ).val)) → ∀ (q : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), q.y = 0 → GlobalTheory.UT.IsTor τ' q.g → QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) q x' → x'.left ≫ u.φ = spMap y₀ ≫ (ρ.pt b).left := by
  first | exact @GlobalTheory.Poinc.ToricLabel.exists_label | exact GlobalTheory.Poinc.ToricLabel.exists_label | (intros; apply GlobalTheory.Poinc.ToricLabel.exists_label <;> assumption)
end
end
