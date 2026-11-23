module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.BaseOnto
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.IdealSplitHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.QuotObjLink
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ActGActGInv
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.AdmissibleOfIntegralConjLe
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.BEtaPt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.SecInjG
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsEtIdealOfPlace
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.BSecInj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ExistsIsoOfCart
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsDominantGenericFibre
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsUnitNatOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.KerAtLift
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LiesAbsHolds
public import Development.AutomorphicArithmetic.CommutativeAlgebra.IsogenyClassExistsOfQuotient
public import Development.AutomorphicArithmetic.CommutativeAlgebra.LatticeGeneration
public import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientLevelOfLatticeGeneration
public import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientMapComp
public import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientModuliObjectExists
public import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientUniqueOfComp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.OClsAt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.OStepF
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PBaseFet
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsQuotTriv
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverCompFinite
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PFEtExt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PNormExt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PQuotOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.StepAHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PairCalc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.TjExGOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.CovLink
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.CovMain

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.BLevOf

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.bLev_of :
    LatB → EtaPtB → UpperTheory.Gal.crystallineComparison.Mod.EtInj → BLev := by
  intro hLat hEta hInj p _ D G L _ E _ _ gb w q _ r 𝔴 𝔫 S k T N₀ 𝔟₁ 𝔟₂ X₁ X₂ 𝔴' i hmax hle hb _ h hint htj M₁ M₂ c₁ c₂ a₁ a₂ n₁ n₂
    C₁ C₂ W f mf _ e _ _ Tj P Ω _ _ x x' hj hy
  have atq' : AtPrime D q r 𝔴' := { S.atq with max := hmax, le := hle }
  refine hInj q (datAt S.atq S.sp) (Ow w) S.b N₀ X₂.lev.1 X₂.lev.2.1 X₂.M 𝔟₂ 1 X₂.Y X₂.π X₂.ov X₂.mπ _ _ _ ?_ ?_
  · have e₁ : ∀ z : Sp Ω ⟶ (T.M M₁).X, (z ≫ W.π ≫ C₂.j) ≫ X₂.π = z ≫ P.y ≫ Tj.t := fun z => by
      rw [P.yt]; simp only [Category.assoc]
    rw [e₁, e₁, reassoc_of% hy]
  · intro y₀
    obtain ⟨x₀, v, hv, e₀⟩ := hLat p D G L q r 𝔴' 𝔟₁ 𝔟₂ i h atq' htj hint hb X₁.lev.2.2.2.2 M₁ M₂ a₁ a₂ n₁.2 n₂.2 y₀
    have key : ∀ z : Sp Ω ⟶ (T.M M₁).X, (z ≫ W.π ≫ C₂.j) ≫ (X₂.Y.lv y₀).left ≫ X₂.mπ.φ =
        (z ≫ ((T.M M₁).univ.eta (algebraMap (𝓞 D.F) D.O a₁ • x₀)).left ≫ P.fa) ≫ Tj.ψ.left ≫ Tj.mt.φ := fun z => by
      have h1 := congrArg (fun g => g.left) (hEta p D G L E gb h (T.M M₁).X (T.M M₁).s M₁ M₂ (T.M M₁).univ W.o W.ψ W.trans Ω z
        (algebraMap (𝓞 D.F) D.O a₁ • x₀) (algebraMap (𝓞 D.F) D.O a₂ • y₀) ⟨v, hv, e₀⟩)
      have ht : (toUnit (Over.mk z)).left = z := by simpa using Over.w (toUnit (Over.mk z))
      simp only [Over.comp_left, ht] at h1
      have h2 := W.φ.eta (algebraMap (𝓞 D.F) D.O a₂ • y₀)
      have h3 := C₂.lv y₀
      simp only [Category.assoc]
      rw [reassoc_of% P.sq, P.mt, reassoc_of% h1, reassoc_of% h2, reassoc_of% h3]
    have sec : ((T.M M₁).univ.eta (algebraMap (𝓞 D.F) D.O a₁ • x₀)).left ≫ (T.M M₁).univ.A.hom = 𝟙 _ := by
      simpa using Over.w ((T.M M₁).univ.eta (algebraMap (𝓞 D.F) D.O a₁ • x₀))
    have hA : x ≫ ((T.M M₁).univ.eta (algebraMap (𝓞 D.F) D.O a₁ • x₀)).left ≫ P.fa =
        x' ≫ ((T.M M₁).univ.eta (algebraMap (𝓞 D.F) D.O a₁ • x₀)).left ≫ P.fa := by
      refine Tj.ms.cart.1.hom_ext ?_ ?_
      · have h4 := C₁.lv x₀
        simp only [Category.assoc]
        rw [P.ms, reassoc_of% h4, reassoc_of% hj]
      · simp only [Category.assoc]
        rw [P.ca.1.w, reassoc_of% sec, hy]
    rw [key x, key x', hA]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.OBaseOnto

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.FiniteEtaleModels.O.baseOnto :
    UpperTheory.Gal.FiniteEtaleModels.BaseOnto := by
  intro p _ D G L hsc E _ _ gb w q _ r 𝔴 𝔫 S k T M c a hnum C Ω _ _ y σ hy
  have hComp : QComp := UpperTheory.quotient_map_comp
  have hCls : ClsEx := UpperTheory.isogeny_class_exists_of_quotient UpperTheory.quotient_moduli_object_exists UpperTheory.quotient_map_comp (UpperTheory.quotient_unique_of_comp UpperTheory.quotient_map_comp)
    (UpperTheory.quotient_level_of_lattice_generation UpperTheory.lattice_generation)
  have hpos : 0 < M.1 := by
    have := M.2.1
    omega
  obtain ⟨o, C', hC'⟩ := UpperTheory.Gal.FiniteEtaleModels.O.clsAt q (datAt S.atq S.sp) hsc.m1 r S.atq.root (Ow w) E S.b gb
    (algebraMap (Ow w) E) S.mat M.1 S.N₀ c a S.𝔞 hnum.1 hpos S.std.cop hnum.2 S.upow S.Y Ω y σ hy
  obtain ⟨x, ⟨hxs, ⟨m⟩⟩, -⟩ := (T.M M).rep (Sp Ω) σ o
  obtain ⟨n', hn'⟩ := (hComp q (datAt S.atq S.sp) (Ow w) E S.b gb M.1 S.N₀ c _ _ _ (T.M M).s S.Y.s S.Y.s
    (T.M M).univ S.Y.univ S.Y.univ C.j (𝟙 _)).2.2.2 (Sp Ω) σ o x m C.m
  have hov : (x ≫ C.j) ≫ S.Y.s = σ ≫ spMap (algebraMap (Ow w) E) := by
    rw [Category.assoc, C.ov, ← Category.assoc, hxs]
  have hlv : ∀ v : (datAt S.atq S.sp).La,
      (o.eta (algebraMap (𝓞 (datAt S.atq S.sp).F) (datAt S.atq S.sp).O a • v)).left ≫ n'.φ =
        (x ≫ C.j) ≫ (S.Y.lv v).left := by
    intro v
    rw [hn', ← Category.assoc]
    refine (congrArg (· ≫ C.m.φ) (m.eta _)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (x ≫ ·) (C.lv v)).trans ?_
    exact (Category.assoc _ _ _).symm
  have hu := (hCls q (datAt S.atq S.sp) (Ow w) E S.b gb (algebraMap (Ow w) E) S.mat M.1 S.N₀ c a S.𝔞 hnum.1 hpos
    S.std.three S.std.cop hnum.2 S.Y (Sp Ω) σ o).2 ⟨x ≫ C.j, hov, n', hlv⟩ C'
  exact ⟨x, hu.1.trans hC', hxs⟩
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PDegGen

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open UpperTheory.Gal.G3 (sp)

namespace UpperTheory.Gal.FiniteEtaleModels

theorem degGen_holds : DegGen := by
  intro E _ Γ _ X O _ _ K₀ K₁ i Y Y' pY π' s h01 hQ0 hQ1 Ω _ _ y σ hy
  let T : ∀ u : Γ, u ∈ K₀ → (X.Z i ⟶ X.Z i) := fun u hu => X.tr i i u (hQ0.adm u hu).1 (hQ0.adm u hu).2
  have hT : ∀ a b (ha : a ∈ K₀) (hb : b ∈ K₀), T a ha ≫ T b hb = T (b * a) (K₀.mul_mem hb ha) :=
    fun a b ha hb => X.tr_mul _ _ _ _ _ _ _ _ _ _ _
  have hTc : ∀ a b (ha : a ∈ K₀) (hb : b ∈ K₀), a = b → T a ha = T b hb := by
    rintro a b ha hb rfl
    rfl
  have h1 : ∀ h1 : (1 : Γ) ∈ K₀, T 1 h1 = 𝟙 _ := fun h1 => X.tr_self _ _ _ _ (X.K i).one_mem
  have hinv1 : ∀ w (hw : w ∈ K₀), w ∈ K₁ → T w hw ≫ π' = π' := fun w hw hw1 =>
    hQ1.inv w hw1 _ _
  have hinv0 : ∀ w (hw : w ∈ K₀), T w hw ≫ π' ≫ s = π' ≫ s := fun w hw => hQ0.inv w hw _ _
  obtain ⟨x, hx⟩ := hQ0.onto Ω y σ hy
  let f : K₀ → { y' // y' ≫ s = y } := fun u =>
    ⟨x ≫ T (u : Γ)⁻¹ (K₀.inv_mem u.2) ≫ π', by
      rw [Category.assoc, Category.assoc, hinv0 _ (K₀.inv_mem u.2), hx]⟩
  have key : ∀ u v : K₀, f u = f v ↔ (u : Γ)⁻¹ * v ∈ K₁ := by
    intro u v
    constructor
    · intro h
      have hv : (x ≫ T (u : Γ)⁻¹ (K₀.inv_mem u.2)) ≫ π' = (x ≫ T (v : Γ)⁻¹ (K₀.inv_mem v.2)) ≫ π' := by
        simpa [f] using congrArg Subtype.val h
      obtain ⟨w, hw1, a, b, he⟩ := hQ1.fib Ω _ _ hv
      have hw0 := h01 hw1
      have he' : x ≫ T (v : Γ)⁻¹ (K₀.inv_mem v.2) = x ≫ T (w * (u : Γ)⁻¹) (K₀.mul_mem hw0 (K₀.inv_mem u.2)) := by
        rw [he, Category.assoc]
        exact congrArg (x ≫ ·) (hT _ _ (K₀.inv_mem u.2) hw0)
      have hm : v.1 * w * (u : Γ)⁻¹ ∈ K₀ := K₀.mul_mem (K₀.mul_mem v.2 hw0) (K₀.inv_mem u.2)
      have hfix : x ≫ T (v.1 * w * (u : Γ)⁻¹) hm = x := by
        have p1 : w * (u : Γ)⁻¹ ∈ K₀ := K₀.mul_mem hw0 (K₀.inv_mem u.2)
        have e1 : T (v.1 * w * (u : Γ)⁻¹) hm = T (w * (u : Γ)⁻¹) p1 ≫ T v.1 v.2 :=
          (hTc _ _ hm (K₀.mul_mem v.2 p1) (by group)).trans (hT _ _ p1 v.2).symm
        have e2 : T (v : Γ)⁻¹ (K₀.inv_mem v.2) ≫ T v.1 v.2 = 𝟙 _ :=
          (hT _ _ (K₀.inv_mem v.2) v.2).trans
            ((hTc _ _ (K₀.mul_mem v.2 (K₀.inv_mem v.2)) K₀.one_mem (by group)).trans (h1 K₀.one_mem))
        rw [e1, ← Category.assoc, ← he', Category.assoc, e2, Category.comp_id]
      have ht := hQ0.free _ hm _ _ Ω x hfix
      have hc := (hQ0.adm _ (K₀.inv_mem u.2)).2 _ ht
      have := K₁.mul_mem (hQ1.le hc) (K₁.inv_mem hw1)
      convert this using 1
      group
    · intro h
      apply Subtype.ext
      show x ≫ T (u : Γ)⁻¹ (K₀.inv_mem u.2) ≫ π' = x ≫ T (v : Γ)⁻¹ (K₀.inv_mem v.2) ≫ π'
      have hk : ((u : Γ)⁻¹ * v)⁻¹ ∈ K₀ := h01 (K₁.inv_mem h)
      have e : T (v : Γ)⁻¹ (K₀.inv_mem v.2) = T (u : Γ)⁻¹ (K₀.inv_mem u.2) ≫ T _ hk :=
        (hTc _ _ (K₀.inv_mem v.2) (K₀.mul_mem hk (K₀.inv_mem u.2)) (by group)).trans
          (hT _ _ (K₀.inv_mem u.2) hk).symm
      rw [e, Category.assoc, hinv1 _ hk (K₁.inv_mem h)]
  let F : K₀ ⧸ K₁.subgroupOf K₀ → { y' // y' ≫ s = y } := Quotient.lift f (fun u v huv =>
    (key u v).2 (Subgroup.mem_subgroupOf.mp (QuotientGroup.leftRel_apply.mp huv)))
  have hinj : Function.Injective F := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H u =>
      induction b using QuotientGroup.induction_on with
      | H v =>
        intro h
        exact QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr ((key u v).1 h))
  have hsurj : Function.Surjective F := by
    rintro ⟨y', hy'⟩
    obtain ⟨x', hx'⟩ := hQ1.onto Ω y' σ (by rw [← Category.assoc, hy', hy])
    obtain ⟨u, hu, a, b, hxe⟩ := hQ0.fib Ω x x' (by rw [hx, ← Category.assoc, hx', hy'])
    refine ⟨QuotientGroup.mk ⟨u⁻¹, K₀.inv_mem hu⟩, ?_⟩
    apply Subtype.ext
    show x ≫ T (u⁻¹)⁻¹ (K₀.inv_mem (K₀.inv_mem hu)) ≫ π' = y'
    rw [hTc (u⁻¹)⁻¹ u (K₀.inv_mem (K₀.inv_mem hu)) hu (inv_inv u), ← Category.assoc]
    rw [← hx', hxe]
  rw [Subgroup.relIndex, Subgroup.index_eq_card]
  exact (Nat.card_congr (Equiv.ofBijective F ⟨hinj, hsurj⟩)).symm

end UpperTheory.Gal.FiniteEtaleModels
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PExtEx

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.extEx_holds :
    MIn → PowProj → ExtEx := by
  intro hM hPP p _ D G hSc E _ _ gb w q _ r 𝔴 𝔫 S N₁ 𝔟 hL
  obtain ⟨h3, hcq, hcp, hsup, hpow⟩ := hL
  obtain ⟨M⟩ := hM.ex q _ (Ow w) S.b N₁ h3 hcq
  have het : IsEtIdeal S.b 𝔟 :=
    (hM.placeOf q _ (Ow w) S.b r 𝔴 S.atq.max S.std.pmem S.std.a1 S.std.ule S.std.tw 𝔟 hsup).2 hpow
  obtain ⟨Y, π, ρ, hov, ⟨m⟩, hG⟩ := hM.finModel q _ (Ow w) S.b N₁ h3 hcq 𝔟 1 het M
  have hfin : IsFinite π := hG.fin
  have het' : Etale π := hG.etale
  have hMp : IsProjOver M.s := hM.proj q _ (Ow w) S.b N₁ h3 hcq hSc.cpt M
  have hYp : IsProjOver Y.s := by
    rw [← hov]
    exact GlobalTheory.isProjOver_comp_of_finite (Ow w) M.X Y.X π M.s hfin hMp
  have hYs : ∃ d, SmoothOfRelativeDimension d Y.s := by
    have h0 := het'
    rw [Etale.iff_smoothOfRelativeDimension_zero] at h0
    have key : ∀ n, SmoothOfRelativeDimension n M.s → SmoothOfRelativeDimension (0 + n) (π ≫ M.s) :=
      fun n hn => inferInstance
    rw [← hov]
    exact ⟨_, key _ M.smooth⟩
  refine ⟨⟨⟨h3, hcq, hcp, hsup, hpow⟩, M, Y, π, hov, m, hfin, het', fun k => ?_, fun k => ?_⟩⟩
  · exact (hPP q _ (Ow w) S.b N₁ h3 hcq Y.X Y.s Y.univ k).1 hYp
  · obtain ⟨d, hd⟩ := hYs
    exact (hPP q _ (Ow w) S.b N₁ h3 hcq Y.X Y.s Y.univ k).2 d hd
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.StepBOf

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.stepB_of :
    TjExG → BRead → BKer → BLev → DescExt → BaseFet → BaseOnto → UpperTheory.Gal.crystallineComparison.Mod.PulledEx → StepB := by
  intro hTj hRead hKer hLev hDesc hFet hOnto hPul p _ D G L sc E _ _ gb w q _ r 𝔴 𝔫 S k T N₀ 𝔟₁ 𝔟₂ X₁ X₂ 𝔴' i hmax hu hb hi h hint htj
    M₁ M₂ c₁ c₂ a₁ a₂ n₁ n₂ _ C₁ C₂ W
  have hq : q.Prime := Fact.out
  obtain ⟨f, ⟨hf, ⟨mf⟩⟩, -⟩ := X₂.M.rep _ _ X₁.Y.univ
  have hqw : (q : 𝓞 D.F) ∈ 𝔴' := hu (Ideal.subset_span (Set.mem_insert _ _))
  have hd : Ideal.absNorm 𝔴' ∣ q ^ Module.finrank ℤ (𝓞 D.F) := by
    have := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem 𝔴').2 hqw)
    rwa [Ideal.absNorm_span_natCast] at this
  obtain ⟨f', -, hf'⟩ := (Nat.dvd_prime_pow hq).1 hd
  have hpos : 0 < f' := Nat.pos_of_ne_zero fun h0 => hmax.ne_top (Ideal.absNorm_eq_one_iff.1 (by simpa [h0] using hf'))
  have he : Ideal.absNorm 𝔴' ^ i = q ^ (f' * i) := by rw [hf', pow_mul]
  have he' : 0 < i → 0 < f' * i := fun h => Nat.mul_pos hpos h
  obtain ⟨Tj⟩ := hTj q (datAt S.atq S.sp) (Ow w) S.b N₀ X₂.lev.1 X₂.lev.2.1 S.std.pmem S.std.m1 r 𝔴' i (f' * i) hmax hu hi he' X₂.M
  obtain ⟨B⟩ := hRead p D G L sc E gb w q r 𝔴 𝔫 S k T N₀ 𝔟₁ 𝔟₂ X₁ X₂ 𝔴' i hmax hu hb hi h hint htj M₁ M₂ c₁ c₂ a₁ a₂ n₁ n₂ C₁ C₂ W f mf hf
    _ he he' Tj
  have k1 := hKer p D G L sc E gb w q r 𝔴 𝔫 S k T N₀ 𝔟₁ 𝔟₂ X₁ X₂ 𝔴' i hmax hu hb hi h hint htj M₁ M₂ c₁ c₂ a₁ a₂ n₁ n₂ C₁ C₂ W f mf hf
    _ he he' Tj B
  have k2 := hLev p D G L sc E gb w q r 𝔴 𝔫 S k T N₀ 𝔟₁ 𝔟₂ X₁ X₂ 𝔴' i hmax hu hb hi h hint htj M₁ M₂ c₁ c₂ a₁ a₂ n₁ n₂ C₁ C₂ W f mf hf
    _ he he' Tj B
  obtain ⟨hfin, het⟩ := hFet p D G L sc E gb w q r 𝔴 _ X₁.site k T M₁ c₁ a₁ n₁ C₁
  have honto := hOnto p D G L sc E gb w q r 𝔴 _ X₁.site k T M₁ c₁ a₁ n₁ C₁
  have hsm : Smooth X₁.Y.s := by
    haveI := X₁.M.smooth
    haveI : Smooth X₁.M.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) X₁.M.s
    haveI := X₁.et
    rw [← X₁.ov]
    infer_instance
  obtain ⟨y', hy, hys⟩ := hDesc (Ow w) E _ _ _ _ X₁.Y.s _ C₁.j C₁.ov hsm hfin het honto f Tj.s B.y Tj.fin B.ys k1
  obtain ⟨P⟩ := hPul q (datAt S.atq S.sp) (Ow w) S.b N₀ X₂.lev.1 X₂.lev.2.1 X₂.M r 𝔴' i _ Tj _ f _ hf X₁.Y.univ mf y' hys
  obtain ⟨t, ht, htπ⟩ := hDesc (Ow w) E _ _ _ _ X₁.Y.s _ C₁.j C₁.ov hsm hfin het honto (y' ≫ Tj.t) X₂.π (W.π ≫ C₂.j) X₂.fin
    (by rw [← Category.assoc C₁.j, hy, B.yt, Category.assoc]) fun Ω _ _ x x' e => k2 Ω x x' e (k1 Ω x x' e)
  have hw : (P.ψ.left ≫ P.m'.φ ≫ Tj.mt.φ) ≫ X₂.M.univ.A.hom = (X₁.Y.univ.A.hom ≫ t) ≫ X₂.π := by
    rw [Category.assoc, Category.assoc, Tj.mt.cart.1.w, ← Category.assoc P.m'.φ, P.m'.cart.1.w, Category.assoc, ← Category.assoc,
      Over.w P.ψ, Category.assoc, htπ]
  have hfa : C₁.m.φ ≫ P.m₀.φ = B.fa := Tj.ms.cart.1.hom_ext
    (by rw [Category.assoc, P.tri, B.ms])
    (by rw [Category.assoc, P.m₀.cart.1.w, ← Category.assoc, C₁.m.cart.1.w, Category.assoc, hy, B.ca.1.w])
  refine ⟨⟨t, ?_, X₂.mπ.cart.1.lift _ _ hw, X₂.mπ.cart.1.lift_snd _ _ _⟩, ht, X₂.mπ.cart.1.hom_ext ?_ ?_⟩
  · rw [← X₂.ov, ← Category.assoc, htπ, Category.assoc, ← Tj.st, ← Category.assoc, hys, hf]
  · rw [Category.assoc, IsPullback.lift_fst, ← Category.assoc P.ψ.left, ← P.sq, Category.assoc, ← Category.assoc, hfa,
      ← Category.assoc, B.sq, Category.assoc, B.mt]
    simp only [Category.assoc]
  · rw [Category.assoc, IsPullback.lift_snd, ← Category.assoc, C₁.m.cart.1.w, Category.assoc, ht]
    simp only [Category.assoc]
    rw [C₂.m.cart.1.w, ← Category.assoc W.φ.φ, W.φ.cart.1.w, Category.assoc, ← Category.assoc W.ψ.left, Over.w W.ψ]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.KsGoodHolds

section

@[expose] public section

namespace UpperTheory.Gal.FiniteEtaleModels

open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.CovMain UpperTheory.Gal.crystallineComparison.Mod

theorem stepA : StepA := stepA_holds (multUnit_of mIn) (latGen_of mIn) (clsEx_of mIn) (trEta_of mIn) (trBack_of mIn) (qComp_of mIn)

theorem baseFet : BaseFet := baseFet_holds (powCart_of mIn) (piFet_of mIn)

theorem stepB : StepB :=
  stepB_of (tjExG_of esNorm_link esGen_link objTri_holds pullIsog_holds pullKer_holds)
    (bRead_of (isogG_of (trEta_of mIn) (trBack_of mIn) (multUnit_of mIn) (trTj_of mIn)) (qObj_of mIn) (qComp_of mIn) objTri_holds)
    (bKer_of (secInjG_of pulledEx_holds pulledRead_holds pullKer_holds kerFromU_holds isoOfKer_holds) (trEtaPt_of mIn))
    (bLev_of latB_holds etaPtB_holds etInj_holds) (descExt_of normExt_holds) baseFet O.baseOnto pulledEx_holds

theorem quotOf : QuotOf := quotOf_holds (powCart_of mIn) (piInv_of mIn) (piFet_of mIn) (piSep_of mIn) (congCRT_of mIn) O.baseOnto

theorem extEx : ExtEx := extEx_holds mIn (powProj_of mIn)

theorem ksGood_holds : KSGood :=
  ksGood_of (siteEx_of mIn) (numEx_of mIn) (clsEx_of mIn) ksCover_holds (piInv_of mIn) (powCart_of mIn) extEx quotOf stepA stepB O.stepF
    degGen_holds fEtExt_holds liesAbs_holds

end UpperTheory.Gal.FiniteEtaleModels
end
end
