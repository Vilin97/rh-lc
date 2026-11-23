module

public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModelTangentOfPullbackTangentStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackTangentLiftOfModelTangentStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfComp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianDvrExtensionsIsoCompatible
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.LinearIndependentBasisCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackGroupPointToModelGroupLinearCombinationStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianMapModelOfIntegralFramedPoint

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_sabMap_model_of_integral_frPt : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (y : FrPt Xo c T.Fr) (x : Sp T.V ⟶ Y.X), spMap (algebraMap T.V T.Fr) ≫ x = GlobalTheory.FlagMod.frX y ≫ Y.j → ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m1 : SABMap t' Xo.univ.t y.x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))), ∃ (ψ : SABMap G Y.t x) (ρ : t'.G.left ⟶ Y.oF.t.G.left), ρ ≫ Y.m0.toSABMap.φ = m1.φ ∧ ρ ≫ Y.oF.t.G.hom = t'.G.hom ≫ GlobalTheory.FlagMod.frX y ∧ ρ ≫ Y.m.φ = m2.φ ≫ ψ.φ := by
  intro E _ _ _ H Dw l Xo c O _ β Y T io
  letI := io.toAlgebra
  intro y x hx G t' m1 m2
  have tr : ∀ {S S' : Scheme.{0}} {s : SAB H S} {s' : SAB H S'} {f g : S' ⟶ S}, f = g → ∀ m : SABMap s' s f,
      ∃ m' : SABMap s' s g, m'.φ = m.φ := by
    intro S S' s s' f g h m
    subst h
    exact ⟨m, rfl⟩
  obtain ⟨m1', hm1⟩ := tr (GlobalTheory.FlagMod.frX_fst y).symm m1
  obtain ⟨ρ, hρ⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m0.toSABMap m1'
  obtain ⟨a, ha⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m ρ
  obtain ⟨a', ha'⟩ := tr hx.symm a
  obtain ⟨G₂, ⟨pull⟩⟩ : ∃ G₂ : SAB H (Sp T.V), Nonempty (SABMap G₂ Y.t x) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull x Y.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨c2, hc2⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ pull a'
  obtain ⟨k, n, hk, hn⟩ := sab_extensions_iso E H Dw l Xo T.V T.Fr y.x G G₂ t' t' m1 m2 m1 c2
  have hk1 : k.φ = 𝟙 _ := by
    apply m1.cart.1.hom_ext
    · rw [Category.id_comp]; exact hk
    · rw [Category.id_comp]; exact k.cart.1.w.trans (Category.comp_id _)
  obtain ⟨b, hb⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ pull n
  obtain ⟨ψ, hψ⟩ := tr (Category.id_comp x) b
  refine ⟨ψ, ρ.φ, by rw [← hρ, hm1], ρ.cart.1.w, ?_⟩
  rw [← ha, ← ha', hc2, hψ, hb, ← Category.assoc, hn, hk1, Category.id_comp]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianMapModelOfIntegralFramedPointStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_semiAbelianMap_model_of_integralFramedPoint : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (y : FrPt Xo c T.Fr) (x : Sp T.V ⟶ Y.X), spMap (algebraMap T.V T.Fr) ≫ x = GlobalTheory.FlagMod.frX y ≫ Y.j → ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m1 : SABMap t' Xo.univ.t y.x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))), ∃ (ψ : SABMap G Y.t x) (ρ : t'.G.left ⟶ Y.oF.t.G.left), ρ ≫ Y.m0.toSABMap.φ = m1.φ ∧ ρ ≫ Y.oF.t.G.hom = t'.G.hom ≫ GlobalTheory.FlagMod.frX y ∧ ρ ≫ Y.m.φ = m2.φ ≫ ψ.φ := by
  first | exact @GlobalTheory.exists_sabMap_model_of_integral_frPt | exact GlobalTheory.exists_sabMap_model_of_integral_frPt | (intros; apply GlobalTheory.exists_sabMap_model_of_integral_frPt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameVectorEqIntegralFrameTangentOnModelStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.frameVector_eq_integralFrameTangent_on_model : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (y : FrPt Xo c T.Fr) (x : Sp T.V ⟶ Y.X) (e : spMap (algebraMap T.V T.Fr) ≫ x = GlobalTheory.FlagMod.frX y ≫ Y.j) (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m1 : SABMap t' Xo.univ.t y.x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))) (ψ : SABMap G Y.t x) (ρ : t'.G.left ⟶ Y.oF.t.G.left), ρ ≫ Y.m0.toSABMap.φ = m1.φ → ρ ≫ Y.oF.t.G.hom = t'.G.hom ≫ GlobalTheory.FlagMod.frX y → ρ ≫ Y.m.φ = m2.φ ≫ ψ.φ → ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) (w : epsOver T.V T.V ⟶ G.G) (u' : Sp (DualNumber T.Fr) ⟶ t'.G.left), u' ≫ m1.φ = y.u τ i → u' ≫ m2.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ w.left → ∀ v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x Y.t.G, (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left = w.left ≫ ψ.φ → GlobalTheory.FlagMod.tanPull (algebraMap T.V T.Fr) e v = GlobalTheory.FlagMod.frVec Y y rfl τ i := by
  intro E _ _ _ H Dw l Xo c O _ β Y T io
  letI := io.toAlgebra
  intro y x e G t' m1 m2 ψ ρ hρ0 hρh hρm τ i w u' hu1 hu2 v hv
  have hb : u' ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
    have : Mono (spMap (algebraMap T.V T.Fr)) := by
      have := IsPreimmersion.of_isLocalization (S := T.Fr) (nonZeroDivisors T.V)
      exact inferInstanceAs (Mono (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))))
    rw [← cancel_mono (spMap (algebraMap T.V T.Fr)), Category.assoc, ← m2.cart.1.w, ← Category.assoc, hu2,
      Category.assoc, Over.w]
    show spMap (dualMap (algebraMap T.V T.Fr)) ≫ spMap (algebraMap T.V (DualNumber T.V)) = _
    rw [spMap_comp', spMap_comp', dualMap_comp_alg]
  refine ((GlobalTheory.FlagMod.toModel_eq_iff _ _ _ _ _).2 ⟨u' ≫ ρ, ?_, ?_, ?_⟩).symm
  · rw [Category.assoc, hρh, ← Category.assoc, hb]
  · rw [Category.assoc, hρ0, hu1]
  · rw [Category.assoc, hρm, ← Category.assoc, hu2,
      GlobalTheory.FlagMod.tanPull_left (algebraMap T.V T.Fr) e v, Category.assoc, hv]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEigenvectorIntegralOfTangentPullbackMem

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TanEigInt

theorem isEigV_of_tanPull_mem : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (x : Sp T.V ⟶ Y.X) (x' : Sp T.Fr ⟶ Y.X) (e : spMap (algebraMap T.V T.Fr) ≫ x = x'), Function.Injective (GlobalTheory.FlagMod.tanPull (G := Y.t.G) (algebraMap T.V T.Fr) e) → ∀ (G : SAB H (Sp T.V)) (ψ : SABMap G Y.t x) (τ : E →+* ℂ) (w : epsOver T.V T.V ⟶ G.G) (v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x Y.t.G), (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left = w.left ≫ ψ.φ → GlobalTheory.FlagMod.tanPull (algebraMap T.V T.Fr) e v ∈ GlobalTheory.FlagMod.eigLie c x' τ → IsEigV c io G τ w := by
  intro E _ _ _ H Dw l Xo c O _ β Y T io x x' e hinj G ψ τ w v hv hmem a z hz
  have h1 : ReciprocityTheory.ChartRestriction.G.PullbackSections.actR Y.t.act a v = z • v := by
    apply hinj
    rw [GlobalTheory.FlagMod.tanPull_actR, map_smulₛₗ, hmem a, hz]
    rfl
  have h2 : (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left ≫ (Y.t.act.act a).left =
      spMap (epsMul z) ≫ (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left :=
    congrArg (fun u => (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv u).left) h1
  have hc : (epsMul z).comp ((algebraMap T.V (DualNumber T.V)).comp (algebraMap T.V T.V)) =
      (algebraMap T.V (DualNumber T.V)).comp (algebraMap T.V T.V) :=
    RingHom.ext fun r => by ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  apply ψ.cart.1.hom_ext
  · rw [Over.comp_left, Category.assoc, ψ.act a, ← Category.assoc, ← hv, h2, hv, Category.assoc]
  · rw [Over.comp_left, Category.assoc, Over.w, Over.w, Category.assoc, Over.w]
    show spMap _ = spMap (epsMul z) ≫ spMap _
    rw [spMap_comp', hc]

end GlobalTheory.TanEigInt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEigenvectorIntegralOfTangentPullbackMemStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isEigenvector_integral_of_tangentPullback_mem : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (x : Sp T.V ⟶ Y.X) (x' : Sp T.Fr ⟶ Y.X) (e : spMap (algebraMap T.V T.Fr) ≫ x = x'), Function.Injective (GlobalTheory.FlagMod.tanPull (G := Y.t.G) (algebraMap T.V T.Fr) e) → ∀ (G : SAB H (Sp T.V)) (ψ : SABMap G Y.t x) (τ : E →+* ℂ) (w : epsOver T.V T.V ⟶ G.G) (v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x Y.t.G), (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left = w.left ≫ ψ.φ → GlobalTheory.FlagMod.tanPull (algebraMap T.V T.Fr) e v ∈ GlobalTheory.FlagMod.eigLie c x' τ → IsEigV c io G τ w := by
  first | exact @GlobalTheory.TanEigInt.isEigV_of_tanPull_mem | exact GlobalTheory.TanEigInt.isEigV_of_tanPull_mem | (intros; apply GlobalTheory.TanEigInt.isEigV_of_tanPull_mem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartFrameChangeDiagonalUnitsIntegralFrame

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

noncomputable section

open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IntFrameDiag

theorem integralFrame_transport : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (x : Sp T.V ⟶ Y.X) (x' : Sp T.Fr ⟶ Y.X) (e : spMap (algebraMap T.V T.Fr) ≫ x = x'), Function.Injective (GlobalTheory.FlagMod.tanPull (G := Y.t.G) (algebraMap T.V T.Fr) e) → ∀ (G : SAB H (Sp T.V)) (ψ : SABMap G Y.t x) (τ : E →+* ℂ) (ub : Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G)), (∀ i, IsTan (ub i)) → (∀ w : epsOver T.V T.V ⟶ G.G, IsTan w → IsEigV c io G τ w → ∃! a : Fin (Dw.mult τ) → T.V, IsComb ub a w) → ∃ ub' : Fin (Dw.mult τ) → ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x Y.t.G, (∀ i, (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (ub' i)).left = (ub i).left ≫ ψ.φ) ∧ ∀ v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x Y.t.G, GlobalTheory.FlagMod.tanPull (algebraMap T.V T.Fr) e v ∈ GlobalTheory.FlagMod.eigLie c x' τ → ∃ a : Fin (Dw.mult τ) → T.V, ∑ i, a i • ub' i = v := by
  intro E _ _ _ H Dw l Xo c O _ β Y T io
  letI := io.toAlgebra
  intro x x' e hinj G ψ τ ub hT hS
  choose ub' hub' using fun i => GlobalTheory.T.exists_modelTangent_of_pullback_tangent x G ψ (ub i) (hT i)
  refine ⟨ub', hub', fun v hv => ?_⟩
  obtain ⟨w, hw, hvw⟩ := GlobalTheory.T.exists_pullback_tangent_lift_of_modelTangent x G ψ v
  obtain ⟨a, ha, -⟩ := hS w hw (GlobalTheory.T.isEigenvector_integral_of_tangentPullback_mem T io x x' e hinj G ψ τ w v hvw hv)
  exact ⟨a, GlobalTheory.T.pullbackGroupPointToModelGroup_linearCombination x G ψ ub ub' a w v hub' hvw ha⟩

theorem diag_unit_of_intFr : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (y' : IntFr Xo c T io) (z : Sp T.V ⟶ X.YY), (X.ptY y'.1 = Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫ z) → ∀ (k : X.F.J), ⊤ ≤ z ⁻¹ᵁ X.F.U k → ∀ (hz : ⊤ ≤ (X.pt y'.1 ≫ X.inc) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), (X.F.ChartFr k (X.pt y'.1 ≫ X.inc) hz Q) → (FrBor t Q y'.1) → ∀ (σ : E →+* ℂ) (i : Fin (Dw.mult σ)), ∃ u : T.Vˣ, algebraMap T.V T.Fr (u : T.V) = (t (some ⟨σ, i⟩) : T.Fr) := by
  intro E _ _ _ H Dw l Xo c Y X T io
  letI := io.toAlgebra
  intro y' z hz0 k hzk hz Q t hQ ht σ i
  have hφ : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
  have hl : X.F.Lies (spMap (algebraMap T.V T.Fr) ≫ z) y'.1 := by
    rw [← show X.ptY y'.1 = spMap (algebraMap T.V T.Fr) ≫ z from hz0]
    exact X.lies_ptY y'.1
  have e : spMap (algebraMap T.V T.Fr) ≫ z ≫ X.π = GlobalTheory.FlagMod.frX y'.1 ≫ Y.j := by
    rw [← Category.assoc]; exact hl.1
  obtain ⟨-, G, t', m1, m2, ⟨ub, hT, -, hS, hU⟩, -⟩ := y'.2
  obtain ⟨ψ, ρ, h1, h2, h3⟩ := GlobalTheory.T.exists_semiAbelianMap_model_of_integralFramedPoint Y T io y'.1 (z ≫ X.π) e G t' m1 m2
  have hx : ⊤ ≤ (z ≫ X.π) ⁻¹ᵁ (X.F.M k).toMChart.U := X.F.inM hzk rfl
  have hx' : ⊤ ≤ (GlobalTheory.FlagMod.frX y'.1 ≫ Y.j) ⁻¹ᵁ (X.F.M k).toMChart.U :=
    e ▸ GlobalTheory.FlagMod.le_preimage_comp _ hx
  have hinj : Function.Injective (GlobalTheory.FlagMod.tanPull (G := Y.t.G) (algebraMap T.V T.Fr) e) := by
    intro u u' huu
    obtain ⟨cv, rfl⟩ := (GlobalTheory.FlagMod.vec (X.F.M k).toMChart _ hx).surjective u
    obtain ⟨cv', rfl⟩ := (GlobalTheory.FlagMod.vec (X.F.M k).toMChart _ hx).surjective u'
    rw [GlobalTheory.FlagMod.tanPull_vec _ _ e hx hx', GlobalTheory.FlagMod.tanPull_vec _ _ e hx hx'] at huu
    have := (GlobalTheory.FlagMod.vec (X.F.M k).toMChart _ hx').injective huu
    congr 1
    funext j
    exact hφ (congrFun this j)
  obtain ⟨ub', hl', hsp⟩ := integralFrame_transport T io (z ≫ X.π) _ e hinj G ψ σ (ub σ) (hT σ) (hS σ)
  have hub : ∀ j, GlobalTheory.FlagMod.tanPull (algebraMap T.V T.Fr) e (ub' j) = GlobalTheory.FlagMod.frVec Y y'.1 rfl σ j := by
    intro j
    obtain ⟨u', hu1, hu2⟩ := hU σ j
    exact GlobalTheory.T.frameVector_eq_integralFrameTangent_on_model T io y'.1 (z ≫ X.π) e G t' m1 m2 ψ ρ h1 h2 h3 σ j (ub σ j) u' hu1 hu2 (ub' j) (hl' j)
  have key : ∀ (w : Sp T.Fr ⟶ X.YY) (_ : w = spMap (algebraMap T.V T.Fr) ≫ z) (hzw : ⊤ ≤ w ⁻¹ᵁ X.F.U k),
      X.F.ChartFr k w hzw Q → X.F.ChartFr k (spMap (algebraMap T.V T.Fr) ≫ z) (GlobalTheory.FlagMod.le_preimage_comp _ hzk) Q := by
    rintro _ rfl _ h
    exact h
  have hQ' := key _ ((X.pt_inc _).trans hz0) hz hQ
  exact (X.top.diag_unit (algebraMap T.V T.Fr) hφ z hzk hl e σ ub' hub hsp hQ' ht).2 i

end GlobalTheory.IntFrameDiag
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartFrameChangeDiagonalUnitsIntegralFrameStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

theorem _root_.GlobalTheory.T.chartFrame_change_diagonal_units_integral_frame : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (y' : IntFr Xo c T io) (z : Sp T.V ⟶ X.YY), (X.ptY y'.1 = Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫ z) → ∀ (k : X.F.J), ⊤ ≤ z ⁻¹ᵁ X.F.U k → ∀ (hz : ⊤ ≤ (X.pt y'.1 ≫ X.inc) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), (X.F.ChartFr k (X.pt y'.1 ≫ X.inc) hz Q) → (FrBor t Q y'.1) → ∀ (σ : E →+* ℂ) (i : Fin (Dw.mult σ)), ∃ u : T.Vˣ, algebraMap T.V T.Fr (u : T.V) = (t (some ⟨σ, i⟩) : T.Fr) := by
  first | exact @GlobalTheory.IntFrameDiag.diag_unit_of_intFr | exact GlobalTheory.IntFrameDiag.diag_unit_of_intFr | (intros; apply GlobalTheory.IntFrameDiag.diag_unit_of_intFr <;> assumption)
end
end
