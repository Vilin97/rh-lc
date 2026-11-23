module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FramePolynomialEquivariantAndNeZero
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilEqIffHermFormEqComplex
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqIffIsometry
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsAnalyticFrameOfAnalyticFibre
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSabMapOfIsAH
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLaws
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ObjMapUniqueOfIsDominant
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibrePrincipalBundleSignEq
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ReadsExistsUniqueTheta
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeByMatricesReflAndComp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePoint
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecValuesComplexFibreAbelianScheme
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnFrameA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExpRowsPf
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Mathlib.Algebra.Azumaya.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsObjMapPhi

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Dict.SameExp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_objMap_phi {D : Datum H} {l : Geo.Tor.Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}}
    {s : S ⟶ Sp B} (o₁ o₂ : Obj D l b s) (m : SABMap o₁.t o₂.t (𝟙 S))
    (h₁ : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
      (o₁.eta a).left ≫ m.φ = (o₂.eta a).left)
    (h₂ : ∀ a, (o₁.etaA a).left ≫ m.φ = (o₂.etaA a).left) :
    ∃ n : ObjMap o₁ o₂ (𝟙 S), n.toSABMap.φ = m.φ := by
  refine ⟨⟨m, fun a => ?_, fun a => (h₂ a).trans (Category.id_comp _).symm⟩, rfl⟩
  have ha : a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) ⊔
      l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) := by
    rw [← Submodule.sup_smul, l.coprime, Submodule.top_smul]
    trivial
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 ha
  rw [o₁.eta_add, o₂.eta_add, o₁.eta_ker x hx, o₂.eta_ker x hx, _root_.one_mul, _root_.one_mul]
  exact (h₁ y hy).trans (Category.id_comp _).symm

theorem phi_eq_of_eq {D : Datum H} {l : Geo.Tor.Level H} {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B}
    {b' : Base l B'} {S : Scheme.{0}} {s : S ⟶ Sp B} {s' : Sp ℂ ⟶ Sp B'}
    {o : Obj D l b s} {o₁ : Obj D l b' s'} {y y' : Sp ℂ ⟶ S} (h : y' = y) (m : ObjMap o₁ o y)
    (m' : ObjMap o₁ o y') : m'.toSABMap.φ = m.toSABMap.φ := by
  subst h
  exact objMap_unique_of_field firstFiveLaws.1.serre m' m

end GlobalTheory.Dict.SameExp



open GlobalTheory.Dict.SameFibre GlobalTheory.Dict.SameExp GlobalTheory.UnifPoint GlobalTheory.AnVal in
theorem GlobalTheory.Dict.anFib_ex_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y y' : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y) (A' : AnFib X bas idx e x L y'), IsSympl X bas → x ∈ X.dom → SelfD X L → l.A = 1 → ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk → A.Marked mk → A'.Marked mk → ∀ z, (A'.ex z).left = (A.ex z).left := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y y' A A' hs hx hL hA mk hmk hm hm' z
  have hyy : y'.x = y.x := anFib_point_eq E H Dw l Xo c hA r g X bas idx e x L y y' A A' hs hx hL mk hmk hm hm'
  obtain ⟨Φ, k₁, -, l₁, m₁, -⟩ := AnFib.exists_anPt E H Dw l Xo c r g X bas idx e x L y A hs hx hL
  obtain ⟨Φ', k₂, -, l₂, m₂, -⟩ := AnFib.exists_anPt E H Dw l Xo c r g X bas idx e x L y' A' hs hx hL
  obtain ⟨-, pos, -⟩ := hx_laws E r X g bas idx 0 hs Even.zero x hx
  let σ : KA l →+* ℂ := (algebraMap c.F ℂ).comp (IntermediateField.inclusion c.le).toRingHom
  have hy : y.x ≫ Xo.s = 𝟙 _ ≫ spMap σ := y.x_over.trans (Category.id_comp _).symm
  have hy' : y'.x ≫ Xo.s = 𝟙 _ ≫ spMap σ := y'.x_over.trans (Category.id_comp _).symm
  obtain ⟨o₁, ⟨n₁⟩⟩ := obj_pull E H Dw l _ ℂ (baseKA l) (baseOfEmb σ) σ _ _ Xo.s (𝟙 _) y.x rfl rfl hy Xo.univ
  obtain ⟨o₂, ⟨n₂⟩⟩ := obj_pull E H Dw l _ ℂ (baseKA l) (baseOfEmb σ) σ _ _ Xo.s (𝟙 _) y'.x rfl rfl hy' Xo.univ
  obtain ⟨u₁, χ₁, b₁, f₁, h₁⟩ := exists_holUnif n₁.toSABMap Φ.toAnFr fun z hz => by rw [m₁]; exact pos z hz
  obtain ⟨u₂, χ₂, b₂, f₂, h₂⟩ := exists_holUnif n₂.toSABMap Φ'.toAnFr fun z hz => by rw [m₂]; exact pos z hz
  obtain ⟨m, hm₀⟩ := exists_sabMap_of_isAH o₁ o₂ u₁ u₂ h₁ h₂ (fun z => by rw [b₁, b₂, l₁, l₂])
    (fun z w => by rw [m₁, m₂]) (fun a => tyAct (fun j => rowType X (idx j)) a)
    (fun a z => OrthoMetric.pt_ext n₁.cart (by
      rw [f₁, Φ.lin, Over.comp_left, Over.comp_left, Category.assoc, n₁.act, ← Category.assoc, f₁]))
    (fun a z => OrthoMetric.pt_ext n₂.cart (by
      rw [f₂, Φ'.lin, Over.comp_left, Over.comp_left, Category.assoc, n₂.act, ← Category.assoc, f₂]))
  obtain ⟨k, hk⟩ := exists_objMap_phi o₁ o₂ m
    (fun a ha => by
      have c₁ : o₁.eta a = u₁.ex _ := OrthoMetric.pt_ext n₁.cart
        ((n₁.eta a).trans ((congrArg (fun q => q.left) ((hm a ha).trans (k₁ _).symm)).trans (f₁ _).symm))
      have c₂ : o₂.eta a = u₂.ex _ := OrthoMetric.pt_ext n₂.cart
        ((n₂.eta a).trans ((congrArg (fun q => q.left) ((hm' a ha).trans (k₂ _).symm)).trans (f₂ _).symm))
      rw [c₁, c₂, hm₀])
    (fun a => by
      have c₁ := o₁.etaA_ker a
      have c₂ := o₂.etaA_ker a
      rw [hA, one_smul] at c₁ c₂
      rw [c₁, c₂, ← CM.HermWeil.ex_zero u₁, ← CM.HermWeil.ex_zero u₂, hm₀])
  obtain ⟨k', hk'⟩ := ((ObjMaps.id_comp_cancel E H Dw l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₂ o₁).2 y'.x (𝟙 _) n₂).1 k
  have hφ := phi_eq_of_eq ((Category.id_comp _).trans hyy) n₁ k'
  have e₁ := congrArg (fun q => q.left) (k₁ z)
  have e₂ := congrArg (fun q => q.left) (k₂ z)
  refine e₂.symm.trans (Eq.trans ?_ e₁)
  refine (f₂ z).symm.trans (Eq.trans ?_ (f₁ z))
  rw [← hm₀ z, Category.assoc, ← hk, ← hk', hφ]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AnalyticFibreMatching

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts


open AlgebraicGeometry CategoryTheory in
theorem GlobalTheory.OneMapRef.exists_scalar_of_marked : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r), IsSympl X bas → x ∈ X.dom → SelfD X L → l.A = 1 → ∀ (y y' : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y) (A' : AnFib X bas idx e x L y') (mk : Dw.La →ₗ[𝓞 E] (Fin r → E)), IsMark l L mk → A.Marked mk → A'.Marked mk → ∀ th th', A.Reads 1 y.s th → A'.Reads 1 y'.s th' → ∃ lam : ℂ, lam ≠ 0 ∧ th' = lam • th ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, evR Xo c f y' = lam ^ n * evR Xo c f y := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L hs hx hL hA y y' A A' mk hmk hm hm' th th' hr hr'
  have he := GlobalTheory.Dict.anFib_ex_eq E H Dw l Xo c r g X bas idx e x L y y' A A' hs hx hL hA mk hmk hm hm'
  have hfr : ∀ j z, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → A'.fr j z = A.fr j z := by
    intro j z hj
    have hch : ∀ z, ∃ i, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U i := fun z => by
      have h : (A.ex z).left (default : PrimeSpectrum ℂ) ∈ ⨆ i, Xo.univ.t.PP.L.U i := by
        rw [Xo.univ.t.PP.isLB.cover]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h
      exact ⟨i, (GlobalTheory.top_le_preimage_iff_mem _ _).2 hi⟩
    choose ch hc using hch
    have hyx : y'.x = y.x := by
      have h1 : (A.ex 0).left ≫ Xo.univ.t.G.hom = y.x := Over.w (A.ex 0)
      have h2 : (A'.ex 0).left ≫ Xo.univ.t.G.hom = y'.x := Over.w (A'.ex 0)
      rw [← h1, ← h2, he]
    have ne' : ∀ j z, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → A'.fr j z ≠ 0 :=
      fun j z h => A'.fr_ne j z (by rw [he]; exact h)
    let q : (Fin g → ℂ) → ℂ := fun z => A.fr (ch z) z / A'.fr (ch z) z
    have key : ∀ j z, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → q z = A.fr j z / A'.fr j z := fun j z h => by
      have hz : ⊤ ≤ (A.ex z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U (ch z)) := fun p hp => ⟨h hp, hc z hp⟩
      have h1 := A.fr_g j (ch z) z hz
      have h2 := A'.fr_g j (ch z) z (by rw [he]; exact hz)
      rw [he] at h2
      rw [h1, h2, mul_div_mul_left _ _ (left_ne_zero_of_mul (h1 ▸ A.fr_ne j z h))]
    have hq : Differentiable ℂ q := fun z0 => by
      have hO : IsOpen {z | ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U (ch z0)} := by
        simpa using (A.hol (Xo.univ.t.PP.L.U (ch z0)) 0).1
      have h' : DifferentiableOn ℂ (A'.fr (ch z0)) {z | ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U (ch z0)} := by
        simpa only [he] using A'.fr_hol (ch z0)
      have hd : DifferentiableOn ℂ q {z | ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U (ch z0)} :=
        ((A.fr_hol (ch z0)).mul (h'.inv fun z hz => ne' _ z hz)).congr fun z hz =>
          (key _ z hz).trans (div_eq_mul_inv _ _)
      exact hd.differentiableAt (hO.mem_nhds (hc z0))
    let pvh : (Fin r → E) →+ (Fin g → ℂ) := AddMonoidHom.mk' (pv X idx x) GlobalTheory.Dict.FrameSign.pv_add
    let P : L →+ (Fin g → ℂ) := pvh.comp L.subtype.toAddMonoidHom
    have hP : Submodule.span ℝ (Set.range P) = ⊤ := by
      rw [← span_image_pv idx hs hx L (TensLat.span_of_selfD X hL)]
      congr 1
      ext w
      exact ⟨fun ⟨a, ha⟩ => ⟨a.1, a.2, ha⟩, fun ⟨a, ha, h⟩ => ⟨⟨a, ha⟩, h⟩⟩
    have hper : ∀ z (a : L), ‖q (z + P a)‖ = ‖q z‖ := fun z a => by
      have h : ⊤ ≤ (A.ex (z + pv X idx x a)).left ⁻¹ᵁ Xo.univ.t.PP.L.U (ch z) := by
        rw [GlobalTheory.Dict.FrameSign.ex_add_pv A z a.2]; exact hc z
      have h1 := A.fr_per a a.2 (ch z) z (hc z)
      have h2 := A'.fr_per a a.2 (ch z) z (by rw [he]; exact hc z)
      change ‖q (z + pv X idx x a)‖ = _
      rw [key _ _ h, key _ _ (hc z), h1, h2, norm_div, norm_div, norm_mul, norm_mul, norm_mul, norm_mul,
        A.χ_norm _ a.2, A'.χ_norm _ a.2,
        mul_div_mul_left _ _ (mul_ne_zero one_ne_zero (norm_ne_zero_iff.2 (Complex.exp_ne_zero _)))]
    have hc0 := ReciprocityTheory.ChartRestriction.G.PullbackSections.norm_periodic_const_range P hP q hq hper z 0
    have h0 : q 0 = 1 := by
      have := A'.fr_0 (ch 0) (by rw [he]; exact hc 0)
      rw [hyx, ← A.fr_0 (ch 0) (hc 0)] at this
      change A.fr (ch 0) 0 / A'.fr (ch 0) 0 = 1
      rw [this, div_self (A.fr_ne _ _ (hc 0))]
    rw [h0, key j z hj] at hc0
    exact ((div_eq_one_iff_eq (ne' j z hj)).1 hc0).symm
  have hyx : y'.x = y.x := by
    have h1 : (A.ex 0).left ≫ Xo.univ.t.G.hom = y.x := Over.w (A.ex 0)
    have h2 : (A'.ex 0).left ≫ Xo.univ.t.G.hom = y'.x := Over.w (A'.ex 0)
    rw [← h1, ← h2, he]
  have hu : y'.u = y.u := funext fun τ => funext fun i => by
    have d := A'.der ⟨τ, i⟩
    simp only [he] at d
    exact ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_unique d (A.der ⟨τ, i⟩)
  obtain ⟨x', hover', u', tan', eig', basis', s', gen'⟩ := y'
  simp only at hyx hu
  subst hyx hu
  obtain ⟨a, ha⟩ := GlobalTheory.Frames.ChgOf.gen_unit' y.s s' y.gen gen'
  refine ⟨a, a.ne_zero, ?_, fun w n f hf => ?_⟩
  · refine (reads_existsUnique_theta E H Dw l Xo c r g X bas idx e x L _ A' hs hx hL 1 s').1.unique hr' ?_
    intro j z pt h1 h2 hj
    rw [he] at h1 hj
    have h3 := hr j z pt h1 h2 hj
    have h4 := (GlobalTheory.sec_values_complex_fibre GlobalTheory.abelianSchemeLaws_all.2.secTwist E H Dw l Xo y.x y.s).1
      a (fun _ => j) pt h2
    refine ((congrArg (Geo.Tor.valAt' pt _) (ha fun _ => j)).trans h4).trans ?_
    rw [hfr j z hj, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact congrArg _ h3
  · let t : Formalism.L2.Pj.Ix Dw → ℂˣ := fun i => match i with
      | none => a
      | some _ => 1
    refine (GlobalTheory.LamT.evR_frChg_tri (inferInstance) hf t (fun _ => 1) (fun τ i j hij => Matrix.one_apply_ne hij.ne)
      (fun τ i => Matrix.one_apply_eq i) (y := y)
      (y' := ⟨y.x, hover', y.u, tan', eig', basis', s', gen'⟩)
      ⟨rfl, ((GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c ℂ y y y).1).2.1,
        (GlobalTheory.Frames.ChgOf.secBC_id_iff y.x _ y.s s').2 ha⟩).trans ?_
    congr 1
    simp [wchar, Fintype.prod_option, t, Formalism.L2.Pj.ex]
end
end
