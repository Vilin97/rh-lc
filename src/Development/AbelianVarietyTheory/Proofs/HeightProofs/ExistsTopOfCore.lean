module

public import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
public import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicGermValueChartIndependent
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThInCuspCusp
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueExistsUniqueOfChartIndependence
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIsNabUncond
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SChartsAndTransferOfGoodLevel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliPartOneStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NsmulMemSmulTop
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Formalism.LocalToGlobal.ProjectiveLattices.DatIndep
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.DegenerationDataAtModelPointOfUniformisation
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DegenerationDataCoordsNeZeroLatticesIsomorphicStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEmbeddingCompleteAlgClosedFixedCarrierStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenOfRangeGenericSubset
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianDvrExtensionsIsoCompatible
import Formalism.LocalToGlobal.ProjectiveLattices.ExtPtUnique
public import Formalism.LocalToGlobal.ProjectiveLattices.ResChPrime
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.UnifAt
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelGoodAndHalfEqPrimeProductStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LocalDataAtConcretePointsExistStatement
public import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemPerGrpOfIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatticePeriodFormIndependentOfModels

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj
open Formalism.MainNotions Formalism.MainNotions.DIV.Cons

namespace GlobalTheory.ModelIndep

theorem norm_unit_eq_one {V C : Type} [CommRing V] [NormedField C] [IsUltrametricDist C] (f : V →+* intO C) (u : Vˣ) :
    ‖((f u : intO C) : C)‖ = 1 := by
  have h1 : ‖((f u : intO C) : C)‖ ≤ 1 := (f u).2
  have h2 : ‖((f (u⁻¹ : Vˣ) : intO C) : C)‖ ≤ 1 := (f (u⁻¹ : Vˣ)).2
  have h3 : ‖((f u : intO C) : C)‖ * ‖((f (u⁻¹ : Vˣ) : intO C) : C)‖ = 1 := by
    rw [← norm_mul, ← Subring.coe_mul, ← map_mul, Units.mul_inv, map_one, Subring.coe_one, norm_one]
  refine le_antisymm h1 ?_
  nlinarith [norm_nonneg ((f u : intO C) : C)]

theorem norm_eq_of_dvr {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] {p : ℕ}
    (hp : p.Prime) (C C' : SCF p) (f : V →+* intO ↥C.S) (f' : V →+* intO ↥C'.S) (r : V) :
    ‖((f r : intO ↥C.S) : ↥C.S)‖ = ‖((f' r : intO ↥C'.S) : ↥C'.S)‖ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have key : ∀ (C : SCF p) (f : V →+* intO ↥C.S) (n : ℕ) (u : Vˣ),
      ‖((f (u * ϖ ^ n) : intO ↥C.S) : ↥C.S)‖ = ‖((f ϖ : intO ↥C.S) : ↥C.S)‖ ^ n := by
    intro C f n u
    rw [map_mul, map_pow, Subring.coe_mul, Subring.coe_pow, norm_mul, norm_pow, norm_unit_eq_one, one_mul]
  have hp0 : (p : V) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  obtain ⟨e, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
  have hpe : ∀ (C : SCF p) (f : V →+* intO ↥C.S), ‖((f ϖ : intO ↥C.S) : ↥C.S)‖ ^ e = (p : ℝ)⁻¹ := by
    intro C f
    rw [← key C f e w, ← hw, map_natCast, ← C.norm_p]
    simp
  have he : e ≠ 0 := by
    rintro rfl
    have h := hpe C f
    rw [pow_zero] at h
    have h2 : (p : ℝ) = 1 := inv_eq_one.1 h.symm
    exact hp.ne_one (by exact_mod_cast h2)
  have hϖ' : ‖((f ϖ : intO ↥C.S) : ↥C.S)‖ = ‖((f' ϖ : intO ↥C'.S) : ↥C'.S)‖ :=
    (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) he).1 ((hpe C f).trans (hpe C' f').symm)
  by_cases hr : r = 0
  · subst hr; simp
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
  rw [key, key, hϖ']

theorem betaAt_eq_of_dvr {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] {p : ℕ}
    (hp : p.Prime) (C C' : SCF p) (f : V →+* intO ↥C.S) (f' : V →+* intO ↥C'.S) (D : DegPre V) (a b : D.X) :
    betaAt D ((intO ↥C.S).subtype.comp f) p a b = betaAt D ((intO ↥C'.S).subtype.comp f') p a b := by
  have h : ∀ χ, vPsiAt D ((intO ↥C.S).subtype.comp f) p χ = vPsiAt D ((intO ↥C'.S).subtype.comp f') p χ := by
    intro χ
    unfold vPsiAt
    split_ifs with h
    · exact congrArg (fun x => -Real.logb p x) (norm_eq_of_dvr hp C C' f f' h.choose)
    · rfl
  simp only [betaAt, h]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_extension {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    {la : HeightOneSpectrum (𝓞 c.F)} (hB : PointsOfFlagModel.BaseAt la β) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ)
    (ho : OverLa la T.V io e) (x : Sp T.Fr ⟶ Xo.X)
    (hxs : x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom))
    (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m1 : SABMap t' Xo.univ.t x)
    (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr)))
    {p : ℕ} {C : SCF p} (Pc : PointsOfFlagModel.PtC Y C) (eF : T.Fr →+* ↥C.S) (g : T.V →+* intO ↥C.S)
    (h1' : eF.comp io = Pc.fK) (h2' : Pc.y ≫ pullback.fst _ _ = spMap eF ≫ x)
    (h3' : ∀ a, ((g a : intO ↥C.S) : ↥C.S) = eF (algebraMap T.V T.Fr a)) :
    ∃ yt : Sp T.V ⟶ Y.X, spMap g ≫ yt = Pc.yt ∧ Nonempty (SABMap G Y.t yt) := by
  obtain ⟨b, hb⟩ := GlobalTheory.EtaVal.exists_base_map_of_overLa (fun a => (hB.2 (β a)).1 ⟨a, rfl⟩) T io e ho
  have hcond : x ≫ Xo.s = spMap io ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [hxs, GlobalTheory.EtaVal.spMap_comp_spMap]
  let z : Sp T.Fr ⟶ Xo.XF c := pullback.lift x (spMap io) hcond
  have hzs : z ≫ pullback.snd _ _ = spMap io := pullback.lift_snd _ _ _
  have hzf : z ≫ pullback.fst _ _ = x := pullback.lift_fst _ _ _
  have hx : z ≫ Y.j ≫ Y.s = Out.jK T.V ≫ spMap b := by
    show z ≫ (Y.jQ ≫ pullback.fst _ _) ≫ Y.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, hzs]
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hb]
  obtain ⟨yt, h1, h2⟩ := extPt Y T b z hx
  obtain ⟨PP', cub, sym, adj, prim, mP, -⟩ := sabPull Out.CubePf.cubePull yt Y.t
  obtain ⟨mF, -⟩ := sabCancel pullCubCancel E H _ _ _ Xo.univ.t Y.oF.t t' (pullback.fst _ _) z Y.m0.toSABMap
    (PullbackSections.sabMapCast m1 hzf.symm)
  obtain ⟨mJ, -⟩ := sabComp pullCubComp E H _ _ _ Y.t Y.oF.t t' (Y.jQ ≫ pullback.fst _ _) z Y.m mF
  have hj : z ≫ Y.jQ ≫ pullback.fst _ _ = Out.jK T.V ≫ yt := h1.symm
  obtain ⟨mK, -⟩ := sabCancel pullCubCancel E H _ _ _ Y.t _ t' yt (Out.jK T.V) mP (PullbackSections.sabMapCast mJ hj)
  obtain ⟨-, ψ, -⟩ := GlobalTheory.sab_extensions_iso E H Dw l Xo T.V T.Fr x G _ t' t' m1 m2 m1 mK
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ Y.t _ G yt (𝟙 _) mP ψ
  have hprY : IsProper Y.s := projProper O Y.X Y.s Y.proj
  have hr : (intO ↥C.S).subtype.comp g = eF.comp (algebraMap T.V T.Fr) := RingHom.ext h3'
  have hy : Pc.y = spMap eF ≫ z := by
    apply pullback.hom_ext
    · rw [h2', Category.assoc, hzf]
    · rw [Pc.y_over, Category.assoc, hzs, GlobalTheory.EtaVal.spMap_comp_spMap, h1']
  have halg : g.comp b = Pc.alg := by
    refine RingHom.ext fun a => Subtype.ext ?_
    have q1 := DFunLike.congr_fun Pc.compat a
    have q2 := DFunLike.congr_fun hb a
    have q3 := DFunLike.congr_fun h1' (β a)
    simp only [RingHom.comp_apply] at q1 q2 q3 ⊢
    rw [h3', q2, q3]; exact q1.symm
  refine ⟨yt, ?_, ⟨PullbackSections.sabMapCast n (Category.id_comp yt)⟩⟩
  refine GlobalTheory.EtaVal.point_ext_of_injective (intO ↥C.S).subtype Subtype.val_injective Y.s _ _ ?_ ?_
  · rw [Pc.ext, hy, Category.assoc, ← h1, ← Category.assoc, GlobalTheory.EtaVal.spMap_comp_spMap, hr,
      ← GlobalTheory.EtaVal.spMap_comp_spMap, Category.assoc]
  · rw [Pc.yt_over, Category.assoc, h2, GlobalTheory.EtaVal.spMap_comp_spMap, halg]

theorem exists_equiv_of_uniformisation {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    {la : HeightOneSpectrum (𝓞 c.F)} (hB : PointsOfFlagModel.BaseAt la β) (T : CDVR) (hT : T.FinRes) (io : c.F →+* T.Fr) (e : ℕ)
    (ho : OverLa la T.V io e) (x : Sp T.Fr ⟶ Xo.X)
    (hxs : x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom))
    (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m1 : SABMap t' Xo.univ.t x)
    (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr)))
    (T' : CDVR) (φ : T.V →+* T'.V) (hφ : Function.Injective φ) (hφf : φ.Finite) (G' : SAB H (Sp T'.V))
    (mG : SABMap G' G (spMap φ)) (U : PELUnif (maximalIdeal T'.V) G')
    (hU : ∀ χ, PsiUnitOn U.D.toPre χ (abLocus G'.G)) (hTo : U.TorsionIso)
    {p : ℕ} (hp : p.Prime) {C : SCF p} (Pc : PointsOfFlagModel.PtC Y C) (eF : T.Fr →+* ↥C.S)
    (h1' : eF.comp io = Pc.fK) (hle : ∀ a : T.V, ‖eF (algebraMap T.V T.Fr a)‖ ≤ 1)
    (hlt : ∀ a ∈ maximalIdeal T.V, ‖eF (algebraMap T.V T.Fr a)‖ < 1)
    (h2' : Pc.y ≫ pullback.fst _ _ = spMap eF ≫ x) (A : DatAt Y Pc) :
    ∃ (f : T'.V →+* intO ↥C.S) (q : U.D.toPre.X ≃ₗ[𝓞 E] A.Ylat),
      ∀ a b, A.beta (q a) (q b) = betaAt U.D.toPre ((intO ↥C.S).subtype.comp f) p a b := by
  let g : T.V →+* intO ↥C.S := (eF.comp (algebraMap T.V T.Fr)).codRestrict _ hle
  have hg : Function.Injective g := fun a b h =>
    IsFractionRing.injective T.V T.Fr (eF.injective (congrArg Subtype.val h))
  obtain ⟨yt, hyt, ⟨n⟩⟩ := exists_extension Y hB T io e ho x hxs G t' m1 m2 Pc eF g h1' h2' (fun _ => rfl)
  have hpm : (p : T.V) ∈ maximalIdeal T.V := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    have h := norm_unit_eq_one g u
    rw [hu, map_natCast] at h
    have h' : ‖(p : ↥C.S)‖ = 1 := by simpa using h
    rw [C.norm_p] at h'
    exact hp.ne_one (by exact_mod_cast inv_eq_one.1 h')
  obtain ⟨f, hf, -, hfl⟩ := (GlobalTheory.T.exists_embedding_completeAlgClosed_fixedCarrier T p hp hT hpm).2 C g T' φ hg hlt hφ hφf
  obtain ⟨n2, -⟩ := sabComp pullCubComp E H _ _ _ Y.t G G' yt (spMap φ) n mG
  have hab : (spMap φ ≫ yt) ⁻¹' abLocus Y.t.G = abLocus G'.G :=
    Set.ext fun q => abLocus_pullback abLocusOne Y.t.semi n2.cart.1 q
  let A₀ : DatAt Y Pc :=
    { R := T'.V
      noeth := inferInstance
      normal := inferInstance
      complete := inferInstance
      «ι» := spMap φ ≫ yt
      f := f
      f_loc := hfl
      fac := by rw [← Category.assoc, GlobalTheory.EtaVal.spMap_comp_spMap, hf, hyt]
      t := G'
      m := n2
      U := U
      unitOn := fun χ => by rw [hab]; exact hU χ
      tors := hTo }
  obtain ⟨-, q, hq⟩ := GlobalTheory.T.degenerationData_coords_ne_zero_lattices_isomorphic E H Dw l Xo c O β Y p C Pc hp T g yt hT hg hlt hyt A₀ A
  exact ⟨f, q, hq⟩

theorem exists_equiv_two_models {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F}
    (Y : Model Xo c β) (Y' : Model Xo c β') {la : HeightOneSpectrum (𝓞 c.F)} (hB : PointsOfFlagModel.BaseAt la β)
    (hB' : PointsOfFlagModel.BaseAt la β') (T : CDVR) (hT : T.FinRes) (io : c.F →+* T.Fr) (e : ℕ)
    (ho : OverLa la T.V io e) (x : Sp T.Fr ⟶ Xo.X)
    (hxs : x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom))
    (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m1 : SABMap t' Xo.univ.t x)
    (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr)))
    {p : ℕ} (hp : p.Prime) {C C' : SCF p} (P : PointsOfFlagModel.PtC Y C) (P' : PointsOfFlagModel.PtC Y' C')
    (eF : T.Fr →+* ↥C.S) (a1 : eF.comp io = P.fK) (a2 : ∀ a : T.V, ‖eF (algebraMap T.V T.Fr a)‖ ≤ 1)
    (a3 : ∀ a ∈ maximalIdeal T.V, ‖eF (algebraMap T.V T.Fr a)‖ < 1)
    (a4 : P.y ≫ pullback.fst _ _ = spMap eF ≫ x)
    (eF' : T.Fr →+* ↥C'.S) (b1 : eF'.comp io = P'.fK) (b2 : ∀ a : T.V, ‖eF' (algebraMap T.V T.Fr a)‖ ≤ 1)
    (b3 : ∀ a ∈ maximalIdeal T.V, ‖eF' (algebraMap T.V T.Fr a)‖ < 1)
    (b4 : P'.y ≫ pullback.fst _ _ = spMap eF' ≫ x) (A : DatAt Y P) (A' : DatAt Y' P') :
    ∃ f : A.Ylat ≃ₗ[𝓞 E] A'.Ylat, ∀ a b, A'.beta (f a) (f b) = A.beta a b := by
  obtain ⟨T', φ, G', mG, hφ, hφf, -, -, U, hU, hTo⟩ :=
    GlobalTheory.UnifAfterExt.exists_finite_ext_uniformised E H Dw l Xo T G t' m2 x m1 hT
  obtain ⟨f, q, hq⟩ := exists_equiv_of_uniformisation Y hB T hT io e ho x hxs G t' m1 m2
    T' φ hφ hφf G' mG U hU hTo hp P eF a1 a2 a3 a4 A
  obtain ⟨f', q', hq'⟩ := exists_equiv_of_uniformisation Y' hB' T hT io e ho x hxs G t' m1 m2
    T' φ hφ hφf G' mG U hU hTo hp P' eF' b1 b2 b3 b4 A'
  refine ⟨q.symm.trans q', fun a b => ?_⟩
  have h1 := hq (q.symm a) (q.symm b)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
  exact (hq' (q.symm a) (q.symm b)).trans ((betaAt_eq_of_dvr hp _ _ f' f _ _ _).trans h1.symm)

theorem datIndep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), DatIndep Xo c := by
  intro E _ _ _ H Dw l Xo c la Tw Tw' hTw hTw' T io e y ho hy z z' hz hz' A A'
  letI := io.toAlgebra
  obtain ⟨y, hy1, G, t', m1, m2, hy2⟩ := y
  obtain ⟨v, C, P, Fl⟩ := z
  obtain ⟨v', C', P', Fl'⟩ := z'
  obtain ⟨hv, eF, a1, a2, a3, a4, -⟩ := hz
  obtain ⟨hv', eF', b1, b2, b3, b4, -⟩ := hz'
  obtain rfl : v = lamOf la := hv
  obtain rfl : v' = lamOf la := hv'
  exact exists_equiv_two_models (Tw.Y (lamOf la)) (Tw'.Y (lamOf la)) (hTw.1 (lamOf la)).1 (hTw'.1 (lamOf la)).1 T hy
    io e ho y.x y.x_over G t' m1 m2 (resCh_prime la) P P' eF a1 a2 a3 a4 eF' b1 b2 b3 b4 A A'

end GlobalTheory.ModelIndep
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatticePeriodFormIndependentOfModelsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.DIV.Cons
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.latticePeriodForm_independent_of_models : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), DatIndep Xo c := by
  first | exact @GlobalTheory.ModelIndep.datIndep | exact GlobalTheory.ModelIndep.datIndep | (intros; apply GlobalTheory.ModelIndep.datIndep <;> assumption)
end
end

-- Source module: Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndNab

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace CIndNab

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

theorem thExpr_eq (hU : ThExprUniqSt) [StarRing (𝓞 E)] (nab nab' : NabV Xo c) (h : IsNab Xo c nab)
    (h' : IsNab Xo c nab') {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {n : ℕ}
    (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmA c a n)
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y.x))) :
    thExpr Xo c nab y P F = thExpr Xo c nab' y P F := by
  letI : Algebra ℚ S := ((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra
  have key : ∀ (K : ℤ) (k : ℕ), K = (k : ℤ) →
      ∀ G : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L K (ptO Xo y.x)),
      ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y K (G b) (colOf m b) =
        ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab' y K (G b) (colOf m b) := by
    rintro K k rfl G
    exact hU E H Dw l Xo c nab nab' h h' S y k n G a P hP
  unfold thExpr
  congr 1
  exact key _ (l.M ^ 2) (Nat.cast_pow l.M 2).symm F

theorem thValAt_iff (hU : ThExprUniqSt) [StarRing (𝓞 E)] (nab nab' : NabV Xo c) (h : IsNab Xo c nab)
    (h' : IsNab Xo c nab') {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {n : ℕ}
    (x : Fin n → Dw.La) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmA c a n)
    (v : S) : ThValAt Xo c nab y x P v ↔ ThValAt Xo c nab' y x P v := by
  constructor
  · rintro ⟨S', i1, i2, φ, y', F, hff, hmap, hvt, hv⟩
    exact ⟨S', i1, i2, φ, y', F, hff, hmap, hvt, hv.trans (thExpr_eq Xo c hU nab nab' h h' y' a P hP F)⟩
  · rintro ⟨S', i1, i2, φ, y', F, hff, hmap, hvt, hv⟩
    exact ⟨S', i1, i2, φ, y', F, hff, hmap, hvt, hv.trans (thExpr_eq Xo c hU nab nab' h h' y' a P hP F).symm⟩

end CIndNab


open CIndNab in
theorem nabUniq_of_chartIndep2 (hC : ChartIndepSt2) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) : NabUniq Xo c := by
  intro _ nab nab' h h' a n _
  have hU := thExprUniq_of_chartIndep2 hC
  refine Set.ext fun f => ⟨?_, ?_⟩
  · rintro ⟨x, P, hP, hf⟩
    exact ⟨x, P, hP, fun p y => (thValAt_iff Xo c hU nab nab' h h' y x a P hP _).1 (hf p y)⟩
  · rintro ⟨x, P, hP, hf⟩
    exact ⟨x, P, hP, fun p y => (thValAt_iff Xo c hU nab nab' h h' y x a P hP _).2 (hf p y)⟩

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCompletionOfCoreSatisfyingLaws

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.DIV.Cons
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Member

theorem exists_completion_of_core_satisfying_laws : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Core D), LawsCore T → (∀ j, 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q) → (∀ j, InR D j → KPsiIn (Dw := T.Q.Dw j) T.Q.c) → (∀ j, InR D j → ∀ (_ : StarRing (𝓞 D.host.E)) (nab : NabV (T.Q.Xo j) T.Q.c), IsNab (T.Q.Xo j) T.Q.c nab → ThInCusp (T.Q.Xo j) T.Q.c nab (T.cuspA j) ∧ (j < D.R.m → ThNe0 (T.Q.Xo j) T.Q.c nab)) → ∃ T' : Top D, LawsP T' ∧ T'.toCore = T := by
  intro hC D T hT hpq hK hth
  obtain ⟨G, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.T.localDataAtConcretePoints_exist D T.Q hT.pins hpq
  have hnab := fun j => GlobalTheory.CanonConn.exists_isNab_uncond D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c
  choose st nab hN using hnab
  have hgood := (GlobalTheory.T.level_good_and_half_eq_prime_product D T.Q.H T.Q.l hT.pins.1.2.1 hT.pins.2.1.1).1
  have hreg := fun j => GlobalTheory.Reg.sCharts_and_transfer_of_good_level GlobalTheory.T.compactifiedModuli_partOne GlobalTheory.Moduli.moduli_scheme_exists
    D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c (hpq j) hgood
  refine ⟨{ toCore := T, G := G, nab := nab,
            dδ := fun j n => noDelta (T.Q.Xo j) T.Q.c (nab j) (GlobalTheory.ObjLower.sabId (T.Q.Xo j).univ.t) n }, ?_, rfl⟩
  exact
    { toLawsCore := hT
      allTest := fun j _ => GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange D.host.E T.Q.H (T.Q.Dw j)
        T.Q.l (T.Q.Xo j) T.Q.c
      reg := fun j _ => (Formalism.L2.PjFree.regP_ofPj (T.U j)).1 ((hreg j).2.1 D.R.r _)
      datum_condition := h1
      tower := h2
      hasData_condition := h3
      points_condition := h4
      lattice_condition := h5
      bc66 := h6
      datIndep := fun j _ _ => GlobalTheory.T.latticePeriodForm_independent_of_models D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c
      nabPin := fun j _ => ⟨st j, hN j⟩
      nabUniq := fun j _ => Formalism.MainNotions.ModuliIntegralCharts.H1.nabUniq_of_chartIndep2 hC (T.Q.Xo j) T.Q.c
      thTot := fun j _ => @GlobalTheory.thValTot_of_chartIndep GlobalTheory.firstFiveLaws.1 hC D.host.E _ _ _ T.Q.H (T.Q.Dw j) T.Q.l
        (T.Q.Xo j) T.Q.c (st j) (nab j) (hN j)
      thCusp := fun j hj => (hth j hj (st j) (nab j) (hN j)).1
      thNe := fun j h1 h2 => (hth j ⟨h1, h2.le⟩ (st j) (nab j) (hN j)).2 h2
      kPsi := hK }

end GlobalTheory.Member
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsTopOfCore

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin

theorem thInCusp_of_laws (D : D7) (T : Core D) (h : LawsM T) (j : ℕ)
    (hj : InR D j) (inst : StarRing (𝓞 D.host.E)) (nab : NabV (T.Q.Xo j) T.Q.c)
    (hn : IsNab (T.Q.Xo j) T.Q.c nab) : ThInCusp (T.Q.Xo j) T.Q.c nab (T.cuspA j) := by
  have hr1 : 1 ≤ D.R.r := by
    have h2 := D.R.two_le_m
    simp only [Ranks.r]; omega
  have hU : ∀ σ, Formalism.L2.PjFree.GoodEmb T.Q.c σ →
      Formalism.L2.PjFree.IsUnf (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) := fun σ hσ =>
    (Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf j hj σ ((Formalism.L2.PjFree.goodEmb_iff σ).1 hσ))
  exact @GlobalTheory.Dict.thInCusp_cusp GlobalTheory.harmonicValue_chart_independent D.host.E _ _ _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r
    (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hr1 hU inst nab hn

theorem exists_top_of_core : ∀ (D : D7) (C : Core D), LawsCore C → (∀ j, 1 ≤ (C.Q.Dw j).p + (C.Q.Dw j).q) → OKPsi D → ∃ T : Top D, LawsP T ∧ T.toCore = C := by
  intro D C hC hpq hK
  exact GlobalTheory.Member.exists_completion_of_core_satisfying_laws GlobalTheory.harmonicValue_chart_independent D C hC hpq (hK C.Q hC.pins) (fun j hj inst nab hn =>
    ⟨thInCusp_of_laws D C hC.toLawsM j hj inst nab hn,
      fun _ => GlobalTheory.ThetaNeZero.thNe0_of_lawsM GlobalTheory.harmonicValue_chart_independent D C hC.toLawsM j hj inst nab hn⟩)

end GlobalTheory.FinalJoin
end
end
