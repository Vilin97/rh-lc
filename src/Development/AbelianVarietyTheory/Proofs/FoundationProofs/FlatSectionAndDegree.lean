module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FibreIff
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EigenvectorLieDegree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FramedFlatCoordinates
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLaw
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsIsComplEigenSubOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisEigen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAbelianGaloisHost
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLieEigenbasisLocalizationAtPrimeStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLieEigenbasisOfLocalizationsAtPrimeStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.NormNum.Parity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
public import Formalism.LocalRingCardinality.DataDIV
import Formalism.LocalRingCardinality.SpanPowerMembership.HasStrictFDerivAtExpZero
public import Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLieEigenbasisBaseChangeLocalAlgebra

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.FlatRow

namespace GlobalTheory.EigBasisLocal

open EigenSplit LieEigen
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD)

theorem eigenBasis_map {O R R' I : Type} [CommRing O] [CommRing R] [CommRing R'] [Finite I]
    {σ : I → O →+* R} (hσ : IsSplitting σ) {n m : ℕ} (ρ : O →+* Module.End R (Fin n → R)) (f : R →+* R')
    (ρ' : O →+* Module.End R' (Fin n → R')) (hf : ∀ a x, f ∘ ρ a x = ρ' a (f ∘ x)) (τ : I)
    (b : Fin m → Fin n → R) (hb : ∀ i, b i ∈ eigenSub ρ (σ τ))
    (H : ∀ c ∈ eigenSub ρ (σ τ), ∃! d : Fin m → R, ∑ i, d i • b i = c) :
    (∀ i, f ∘ b i ∈ eigenSub ρ' (f.comp (σ τ))) ∧
      ∀ c ∈ eigenSub ρ' (f.comp (σ τ)), ∃! d : Fin m → R', ∑ i, d i • (f ∘ b i) = c := by
  let _ := f.toAlgebra
  let F : (Fin n → R) →ₗ[R] (Fin n → R') := (Algebra.linearMap R R').compLeft (Fin n)
  have hF : IsBaseChange R' F := IsBaseChange.finitePow (Fin n) (IsBaseChange.linearMap R R')
  have hf' : ∀ a x, F (ρ a x) = ρ' a (F x) := hf
  have hB := isBaseChange_eigenMapAlgebra hσ hf' hF τ
  let b' : Fin m → eigenSub ρ (σ τ) := fun i => ⟨b i, hb i⟩
  have key : ∀ c : eigenSub ρ (σ τ), ∃! d, Fintype.linearCombination R b' d = c := fun c => by
    refine (existsUnique_congr fun d => ?_).1 (H _ c.2)
    rw [Subtype.ext_iff, Fintype.linearCombination_apply]
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
    rfl
  let B : Module.Basis (Fin m) R (eigenSub ρ (σ τ)) :=
    Module.Basis.ofEquivFun (LinearEquiv.ofBijective _ ((Function.bijective_iff_existsUnique _).2 key)).symm
  have hBi : ∀ i, (B i : Fin n → R) = b i := fun i => by
    simp [B, b', Module.Basis.coe_ofEquivFun, Fintype.linearCombination_apply_single]
  let B' := hB.basis B
  have hB' : ∀ i, (B' i : Fin n → R') = f ∘ b i := fun i => by
    rw [← hBi, IsBaseChange.basis_apply]
    rfl
  refine ⟨fun i => hB' i ▸ (B' i).2, fun c hc => ?_⟩
  have k : ∀ d : Fin m → R', ∑ i, d i • (f ∘ b i) = c ↔ B'.equivFun ⟨c, hc⟩ = d := fun d => by
    rw [← LinearEquiv.eq_symm_apply, Module.Basis.equivFun_symm_apply, Subtype.ext_iff, eq_comm]
    simp [hB']
  simp only [k]
  exact existsUnique_eq'

theorem isEigBasis_iff {O R : Type} [CommRing O] [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    {n m : ℕ} {e : Fin n → (epsR R ⟶ G)} (he : IsLieBasis e) {act : OAct O G}
    {ρ : O →+* Module.End R (Fin n → R)} (hρ : ∀ a c, prodPts (ρ a c) e = prodPts c e ≫ act.act a)
    (χ : O →+* R) (b : Fin m → Fin n → R) :
    EigenvectorLieDegree.IsEigBasis act χ (fun i => prodPts (b i) e) ↔ (∀ i, b i ∈ eigenSub ρ χ) ∧
      ∀ c ∈ eigenSub ρ χ, ∃! d : Fin m → R, ∑ i, d i • b i = c := by
  have mem : ∀ c, EigenvectorLieDegree.IsEigVec act χ (prodPts c e) ↔ c ∈ eigenSub ρ χ := fun c => by
    rw [mem_eigenSub]
    refine (and_iff_right (isTangent_prodPts he.1 c)).trans (forall_congr' fun a => ?_)
    rw [← hρ, ← (prodPts_injective he).eq_iff]
    rw [prodPts_smul, Over.OverMorphism.ext_iff]
    rfl
  have cb : ∀ d c, IsLieComb d (fun i => prodPts (b i) e) (prodPts c e) ↔ ∑ i, d i • b i = c := fun d c => by
    refine (Chart.isLieComb_iff d _ _).trans ?_
    rw [prodPts_prodPts he.1, eq_comm]
    exact (prodPts_injective he).eq_iff
  refine and_congr (forall_congr' fun i => mem _) ⟨fun h c hc => ?_, fun h w hw => ?_⟩
  · exact (existsUnique_congr fun d => cb d c).1 (h _ ((mem c).2 hc))
  · obtain ⟨c, rfl⟩ := exists_prodPts he hw.1
    exact (existsUnique_congr fun d => cb d c).2 (h _ ((mem c).1 hw))

theorem isEigBasis_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (l : Level H) (c : Coeff l) (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] (j : c.F →+* R) (g : R →+* R') (t : SAB H (Sp R)) (t' : SAB H (Sp R')) (n : SABMap t' t (spMap g)) (τ : E →+* ℂ) (m : ℕ) (v : Fin m → (epsR R ⟶ t.G)) (v' : Fin m → (epsR R' ⟶ t'.G)), EigenvectorLieDegree.IsEigBasis t.act (FramedFlatCoordinates.chr c τ j) v → (∀ i, IsVecOver g n.φ (v i) (v' i)) → EigenvectorLieDegree.IsEigBasis t'.act (FramedFlatCoordinates.chr c τ (g.comp j)) v' := by
  classical
  intro E _ _ _ H l c R R' _ _ _ j g t t' n τ m v v' hv hv'
  let σ₀ : (E →+* ℂ) → 𝓞 E →+* c.F := fun τ =>
    (τ.codRestrict c.F.toSubfield (c.conj τ)).comp (algebraMap (𝓞 E) E)
  have hσ₀ : Function.Injective σ₀ := fun τ τ' h =>
    (isSplitting_complex E).injective
      (RingHom.ext fun a => congrArg Subtype.val (RingHom.congr_fun h a))
  have hσ : IsSplitting fun τ => j.comp (σ₀ τ) :=
    isSplitting_of_isDomain hσ₀ (NumberField.Embeddings.card E ℂ) j (by
      simpa using (isUnit_discr_of_charZero (E := E) c.F).map j)
  obtain ⟨N, e, he⟩ := Chart.exists_isLieBasis t.G t.semi.smooth
  obtain ⟨e', he', ee⟩ := exists_isLieBasis_baseChange R R' g _ _ _ n.cart t.semi.smooth N e he
  obtain ⟨ρ, hρ⟩ := exists_action he t.act
  obtain ⟨ρ', hρ'⟩ := exists_action he' t'.act
  choose b hb using fun i => exists_prodPts he (hv.1 i).1
  obtain rfl : v = fun i => prodPts (b i) e := (funext hb).symm
  obtain rfl : v' = fun i => prodPts (g ∘ b i) e' := funext fun i =>
    Over.OverMorphism.ext (n.cart.1.hom_ext ((hv' i).trans (prodPts_left n.cart ee _).symm)
      ((Over.w _).trans (Over.w _).symm))
  obtain ⟨h1, h2⟩ := (isEigBasis_iff he hρ _ b).1 hv
  exact (isEigBasis_iff he' hρ' _ _).2
    (eigenBasis_map hσ ρ g ρ' (action_baseChange n.cart he' ee n.act hρ hρ') τ b h1 h2)

end GlobalTheory.EigBasisLocal
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLieEigenbasisBaseChangeLocalAlgebraStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.FlatRow

theorem _root_.GlobalTheory.T.isLieEigenbasis_baseChange_localAlgebra : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (l : Level H) (c : Coeff l) (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] (j : c.F →+* R) (g : R →+* R') (t : SAB H (Sp R)) (t' : SAB H (Sp R')) (n : SABMap t' t (spMap g)) (τ : E →+* ℂ) (m : ℕ) (v : Fin m → (epsR R ⟶ t.G)) (v' : Fin m → (epsR R' ⟶ t'.G)), EigenvectorLieDegree.IsEigBasis t.act (FramedFlatCoordinates.chr c τ j) v → (∀ i, IsVecOver g n.φ (v i) (v' i)) → EigenvectorLieDegree.IsEigBasis t'.act (FramedFlatCoordinates.chr c τ (g.comp j)) v' := by
  first | exact @GlobalTheory.EigBasisLocal.isEigBasis_baseChange | exact GlobalTheory.EigBasisLocal.isEigBasis_baseChange | (intros; apply GlobalTheory.EigBasisLocal.isEigBasis_baseChange <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.TraitDataOfDataAtTraits

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TraitDataOfIntrinsic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section
variable {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''}

theorem map_comp {f : S' ⟶ S} {g : S'' ⟶ S'} {k : S'' ⟶ S} (m' : SABMap t'' t' g) (m : SABMap t' t f)
    (h : g ≫ f = k) : ∃ n : SABMap t'' t k, n.φ = m'.φ ≫ m.φ := by
  subst h
  exact ObjMaps.exists_sab_comp m m'

theorem map_cancel {f : S' ⟶ S} {g : S'' ⟶ S'} {k : S'' ⟶ S} (n : SABMap t'' t k) (m : SABMap t' t f)
    (h : g ≫ f = k) : ∃ m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ := by
  subst h
  exact ObjMaps.exists_sab_cancel m n

end

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

end GlobalTheory.TraitDataOfIntrinsic
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.FlatSectionAndDegree

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory.FlatRow

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}

theorem eigStable {S : Scheme.{0}} (T : SAB H S) (c : Coeff l) : EigStable T c := by
  intro R R' _ _ g j x τ m v v' hv hv'
  obtain ⟨t, ⟨n⟩⟩ := exists_sab x T
  obtain ⟨t', ⟨n'⟩⟩ := exists_sab (spMap g) t
  obtain ⟨n'', e''⟩ := TraitDataOfIntrinsic.map_comp n' n rfl
  choose w hw using fun i => exists_lift n.cart (v i)
  choose w' hw' _ using fun i => existsUnique_isVecOver n'.cart.1 (w i)
  have hb := ((fibre_iff n.cart hw).2 n.act _).2 hv
  refine ((fibre_iff n''.cart (v := w') fun i => ?_).2 n''.act _).1 (GlobalTheory.T.isLieEigenbasis_of_localizations_atPrime E H R' t' _ m w' fun q _ => ?_)
  · change _ ≫ n''.φ = _
    rw [e'', ← Category.assoc, hw' i, Category.assoc, hw, hv']
  let p := q.comap g
  let gp : Localization.AtPrime p →+* Localization.AtPrime q := Localization.localRingHom p q g rfl
  have hg : gp.comp (algebraMap R _) = (algebraMap R' _).comp g :=
    RingHom.ext fun z => Localization.localRingHom_to_map p q g rfl z
  obtain ⟨tq, ⟨nq⟩⟩ := exists_sab (spMap (algebraMap R' (Localization.AtPrime q))) t'
  obtain ⟨tp, ⟨np⟩⟩ := exists_sab (spMap (algebraMap R (Localization.AtPrime p))) t
  obtain ⟨k, ek⟩ := TraitDataOfIntrinsic.map_comp nq n' rfl
  obtain ⟨k', ek'⟩ := TraitDataOfIntrinsic.map_cancel (g := spMap gp) k np
    (by rw [spMap_comp_spMap, spMap_comp_spMap, hg])
  choose wq hq _ using fun i => existsUnique_isVecOver nq.cart.1 (w' i)
  choose wp hp _ using fun i => existsUnique_isVecOver np.cart.1 (w i)
  refine ⟨tq, nq, wq, hq, ?_⟩
  have h₁ := GlobalTheory.T.isLieEigenbasis_localization_atPrime E H R p t tp np _ m w wp hb hp
  have h₂ := GlobalTheory.T.isLieEigenbasis_baseChange_localAlgebra E H l c _ _ ((algebraMap R _).comp j) gp tp tq k' τ m wp wq h₁ fun i =>
    EllComp.isVecOver_cancel np.cart.1 k'.cart.1 (hp i)
      (by rw [← ek', ek, hg]; exact EllComp.isVecOver_comp (hw' i) (hq i))
  rwa [← RingHom.comp_assoc, hg] at h₂

variable {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {U : (Xo.XF c).Opens} {τ : E →+* ℂ}

theorem isIso_fst (Y : Model Xo c (RingHom.id c.F)) : IsIso (pullback.fst Y.s (spMap (RingHom.id c.F))) := by
  have : IsIso (spMap (RingHom.id c.F)) := by
    rw [show spMap (RingHom.id c.F) = 𝟙 _ from Spec.map_id _]; infer_instance
  infer_instance

theorem isNormal_genFibre (Y : Model Xo c (RingHom.id c.F)) : Geo.Tor.IsNormalScheme (FramedFlatCoordinates.genFibre Y) := by
  intro x
  have := isIso_fst Y
  let e := (asIso ((pullback.fst Y.s (spMap (RingHom.id c.F))).stalkMap x)).commRingCatIsoToRingEquiv
  obtain ⟨h₁, h₂⟩ := Y.normal (pullback.fst Y.s (spMap (RingHom.id c.F)) x)
  exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩

theorem comb_one {R : Type} [CommRing R] {t : SAB H (Sp R)} {m : ℕ} {v : Fin m → (epsR R ⟶ t.G)}
    (hv : ∀ i, IsTangent (v i)) (i : Fin m) : IsLieComb ((1 : Matrix (Fin m) (Fin m) R) i) v (v i) := by
  have : (1 : Matrix (Fin m) (Fin m) R) i = Pi.single i 1 := by
    ext k; simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [this]
  exact (LieComb.lieComb_algebra _ _ m v hv).2.2.2.1 i

section Algebraic

variable {L : Type} [Field L] [NumberField L] {j : c.F →+* L} {a : FramedFlatCoordinates.Framed Y U τ L j} {y : Sp L ⟶ Xo.XF c}
  {sig : FramedFlatCoordinates.Rule Y U τ}

end Algebraic

section Ties

variable {D : D7} {X : DivX D} (Lc : placeRankTwoOne.Loc D X) {j : ℕ} {Z : X.Comp j} {τ : D.what₂.Tau}
  {H : Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {Y : Model Xo c (RingHom.id c.F)} {U : (Xo.XF c).Opens} {em : c.F →+* D.what₂.LL}
  (Φ : FramedFlatCoordinates.sections Y U (DV.tauEmb D τ) →ₛₗ[em] X.geo.Fn (X.Yv j Z))

end Ties

end GlobalTheory.FlatRow
end
end
end
