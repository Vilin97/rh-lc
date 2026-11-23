module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SmulMemRatForms
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRamificationOverPlaceOfCdvrReadingInCp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckePointIntegralUpToUnitsAnyAlgClosedField
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckePointLawsOfTransport
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatrices
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtGMulVec
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCDVRFractionFieldReadingInCpFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitHeckePrimeOffLevelOfHeckeIndexPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckePointLaws
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckePrimeDetection

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRamificationOverPlaceOfCdvrReadingInCpStatement

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie

theorem _root_.GlobalTheory.T.exists_ramification_overPlace_of_cdvrReadingInCp : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p]) (T : CDVR) (io : F →+* T.Fr) (k : T.Fr →+* ℂ_[p]), IsReading φ T io k → ∃ e : ℕ, OverLa (placeAt φ) T.V io e := by
  first | exact @GlobalTheory.ReadingOver.overLa_placeAt | exact GlobalTheory.ReadingOver.overLa_placeAt | (intros; apply GlobalTheory.ReadingOver.overLa_placeAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckePointIntegralUpToUnitsAnyAlgClosedFieldStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.heckePoint_integral_upToUnits_anyAlgClosedField : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) (𝔓 : Ideal (𝓞 E)) (p i : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime H l 𝔓 p → (p : 𝓞 c.F) ∉ la.asIdeal → ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ y : IntFr Xo c T io, algCls Xo c T io y → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω], letI := io.toAlgebra; ∀ k : T.Fr →ₐ[c.F] Ω, ∀ yΩ : FrPt Xo c Ω, FrMap k y.1 yΩ → ∀ (C : hkKer (Xo := Xo) 𝔓 p i Ω yΩ) (z : FrPt Xo c Ω), hkRelFr 𝔓 p i (GlobalTheory.ThetaTrace.hkTr Xo c p) Ω yΩ C z → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsIntegralUpToUnits (GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.trivialClassCondition Xo c) T io k.toRingHom z := by
  first | exact @GlobalTheory.HkAnyFieldOf.heckeFrameInt_anyField_of | exact GlobalTheory.HkAnyFieldOf.heckeFrameInt_anyField_of | (intros; apply GlobalTheory.HkAnyFieldOf.heckeFrameInt_anyField_of <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeQuotientFrameChangeOfTriangularFrameChange

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori GlobalTheory.HeckeFrCompare GlobalTheory.HeckePointLaw

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeckeBorelChange

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem isLieImg_comb {Ω : Type} [Field Ω] {x x' : Sp Ω ⟶ Xo.X} {ψ : Gx x ⟶ Gx x'} (hψ : IsLinHom ψ) {p m : ℕ}
    {v v' : Fin m → (Sp (DualNumber Ω) ⟶ Xo.univ.t.G.left)} (hv : ∀ j, IsLieImg p ψ (v j) (v' j))
    (cf : Fin m → Ω) {w w' : Sp (DualNumber Ω) ⟶ Xo.univ.t.G.left} (htw : IsTanAt x w) (htw' : IsTanAt x' w')
    (hw : IsCombAt x v cf w) (hw' : IsCombAt x' v' cf w') : IsLieImg p ψ w w' := by
  let A : Fin m → (tEps x ⟶ Xo.univ.t.G) := fun j => Over.homMk (v j) (hv j).1.1
  let B : Fin m → (tEps x' ⟶ Xo.univ.t.G) := fun j => Over.homMk (v' j) (hv j).2.1.1
  let W : tEps x ⟶ Xo.univ.t.G := Over.homMk w htw.1
  let W' : tEps x' ⟶ Xo.univ.t.G := Over.homMk w' htw'.1
  have hAB : ∀ j, scaleAt x' (p : Ω) ≫ B j = tanMap hψ (A j) := fun j => by
    obtain ⟨-, -, a, ha, e⟩ := hv j
    have : a = A j := Over.OverMorphism.ext ha
    subst this
    exact Over.OverMorphism.ext e
  have hW : (List.ofFn fun i => scaleAt x (cf i) ≫ A i).prod = W := (isCombAt_iff A cf W).1 hw
  have hW' : (List.ofFn fun i => scaleAt x' (cf i) ≫ B i).prod = W' := (isCombAt_iff B cf W').1 hw'
  let Lc : (tEps x' ⟶ Xo.univ.t.G) →* (tEps x' ⟶ Xo.univ.t.G) :=
    MonoidHom.mk' (fun b => scaleAt x' (p : Ω) ≫ b) fun b b' => MonObj.comp_mul _ _ _
  have key : scaleAt x' (p : Ω) ≫ W' = tanMap hψ W := by
    have e1 : scaleAt x' (p : Ω) ≫ W' = Lc W' := rfl
    rw [e1, ← hW, ← hW', map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
    refine congrArg (fun f => (List.ofFn f).prod) (funext fun i => ?_)
    simp only [Function.comp_apply, Lc, MonoidHom.mk'_apply]
    rw [tanMap_scale, ← hAB, ← Category.assoc, ← Category.assoc, scaleAt_comm]
  exact ⟨htw, htw', W, rfl, congrArg (·.left) key⟩

theorem scal_mul'' {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a b : S) (i : (PPx x).ι) :
    scal x (a * b) i = scal x a i * scal x b i := by
  simp only [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_mul]

theorem scal_one'' {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) : scal x (1 : S) i = 1 := by
  simp only [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_one]

theorem secBC_self {Ω : Type} [CommRing Ω] {x : Sp Ω ⟶ Xo.X} {a : Ω} {s s' : LB.Sec (PPx x)}
    (h : GlobalTheory.Frames.SecBC (RingHom.id Ω) a x x s s') : ∀ i, s'.f i = scal x a i * s.f i := by
  obtain ⟨pm, h₁, h₂, h₃⟩ := h
  have e0 : spMap (RingHom.id Ω) = 𝟙 (Sp Ω) := by simp [spMap]
  obtain rfl : pm = 𝟙 _ := gx_ext (h₂.trans (by rw [e0]; simp))
    (h₁.trans (Category.id_comp _).symm)
  intro i
  have e : Scheme.Hom.appLE (𝟙 (Gx x)) ((PPx x).U i) ((PPx x).U i) le_rfl = 𝟙 _ := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    exact (Category.id_comp _).trans (CategoryTheory.Functor.map_id _ _)
  have := h₃ i le_rfl
  rw [e] at this
  exact this.symm

end SlopeTestRemainingChoices

theorem hkRelFr_frBor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime H l P p → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (t : Ix Dw → Ωˣ) (w z : FrPt Xo c Ω), FrBor t w z → ∀ (C : hkKer (Xo := Xo) P p i Ω z) (z' : FrPt Xo c Ω), hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) Ω z C z' → ∃ (C₀ : hkKer (Xo := Xo) P p i Ω w) (w' : FrPt Xo c Ω), hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) Ω w C₀ w' ∧ FrBor t w' z' := by
  intro E _ _ _ H Dw l Xo c P p i hP Ω _ _ _ t w z hb C z' hz
  have hsp : IsSplitOff l P p := hP
  obtain ⟨g, hg0, hgd, hgc⟩ := (GlobalTheory.Frames.frBor_iff_frChg w z t).1 hb
  have hdet : ∀ τ, IsUnit (g τ).det := fun τ =>
    GlobalTheory.Frames.lowerTri_isUnit_det _ (hg0 τ) fun j => by rw [hgd]; exact Units.isUnit _
  have hdet' : ∀ τ, IsUnit ((g τ)⁻¹).det := fun τ => by
    rw [Matrix.det_nonsing_inv]; exact (hdet τ).ringInverse
  obtain ⟨w', hw', -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c Ω z' (fun τ => (g τ)⁻¹) (t none)⁻¹ hdet'
  have hdiag : ∀ τ j, (g τ)⁻¹ j j = ((t⁻¹ (some ⟨τ, j⟩) : Ωˣ) : Ω) := fun τ j => by
    have e := GlobalTheory.Frames.lowerTri_mul_diag ((g τ)⁻¹) (g τ) (GlobalTheory.Frames.lowerTri_inv _ (hg0 τ) (hdet τ)) (hg0 τ) j
    rw [Matrix.nonsing_inv_mul _ (hdet τ), Matrix.one_apply_eq, hgd] at e
    rw [Pi.inv_apply, Units.val_inv_eq_inv_val]
    exact eq_inv_of_mul_eq_one_left e.symm
  have hb' : FrBor t⁻¹ z' w' := (GlobalTheory.Frames.frBor_iff_frChg z' w' t⁻¹).2
    ⟨fun τ => (g τ)⁻¹, fun τ => GlobalTheory.Frames.lowerTri_inv _ (hg0 τ) (hdet τ), hdiag, hw'⟩
  have hbw : FrBor t w' z' := by
    simpa using (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c Ω z' w' w').2.2.2 t⁻¹ hb'
  obtain ⟨ψ, hiso, hlie, hth⟩ := (hkPt_iff hsp _ z C.1 z').1 hz
  obtain ⟨hx, hc, hs⟩ := hgc
  obtain ⟨hx', hc', hs'⟩ := hw'
  obtain ⟨zx, zo, zu, ztan, zeig, zbas, zs, zgen⟩ := z
  dsimp only at hx
  subst hx
  obtain ⟨zx', zo', zu', ztan', zeig', zbas', zs', zgen'⟩ := z'
  dsimp only at hx'
  subst hx'
  refine ⟨C, w', (hkPt_iff hsp _ w C.1 w').2 ⟨ψ, hiso, fun τ j => ?_, ?_⟩, hbw⟩
  · have hcomb : IsCombAt w.x (zu τ) ((g τ)⁻¹ j) (w.u τ j) := by
      obtain ⟨a, ha, -⟩ := zbas τ (w.u τ j) (w.tan τ j) (w.eig τ j)
      have h1 := GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo Ω w.x (w.u τ) (w.tan τ) (zu τ) (g τ).transpose a
        (w.u τ j) (fun k => hc τ k) ha
      have h2 := Formalism.L2.PjFree.isCombAt_single (w.tan τ) j
      have e : (g τ).transpose.mulVec a = Pi.single j 1 :=
        (w.basis τ (w.u τ j) (w.tan τ j) (w.eig τ j)).unique h1 h2
      have ea : a = (g τ)⁻¹ j := by
        have e2 := congrArg ((g τ).transpose⁻¹.mulVec) e
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (by rw [Matrix.det_transpose]; exact hdet τ),
          Matrix.one_mulVec, Matrix.mulVec_single_one] at e2
        rw [e2, ← Matrix.transpose_nonsing_inv]
        ext k
        rfl
      exact ea ▸ ha
    exact isLieImg_comb hiso.2.1 (fun k => hlie τ k) ((g τ)⁻¹ j) (w.tan τ j) (w'.tan τ j) hcomb (hc' τ j)
  · have hth' : GlobalTheory.ThetaTrace.IsThetaTrace Xo.univ.t.G Xo.univ.t.PP ψ p zs zs' := by
      have := hth
      simp only [GlobalTheory.ThetaTrace.hkTr, Equiv.apply_symm_apply] at this
      exact this
    show GlobalTheory.ThetaTrace.IsThetaTrace Xo.univ.t.G Xo.univ.t.PP (conj w.x w'.x ((conj w.x w'.x).symm ψ)) p w.s w'.s
    rw [Equiv.apply_symm_apply]
    have hs₁ := secBC_self hs
    have hs₂ := secBC_self hs'
    refine GlobalTheory.ThetaTrace.IsThetaTrace.smul hth' (toΓ Ω (((t none)⁻¹ : Ωˣ) : Ω)) (fun k => ?_) (fun k => hs₂ k)
    show w.s.f k = scal w.x (((t none)⁻¹ : Ωˣ) : Ω) k * zs.f k
    rw [hs₁ k, ← _root_.mul_assoc, ← scal_mul'', Units.inv_mul, scal_one'', _root_.one_mul]

end GlobalTheory.HeckeBorelChange
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeQuotientFrameChangeOfTriangularFrameChangeStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.heckeQuotient_frame_change_of_triangular_frame_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime H l P p → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (t : Ix Dw → Ωˣ) (w z : FrPt Xo c Ω), FrBor t w z → ∀ (C : hkKer (Xo := Xo) P p i Ω z) (z' : FrPt Xo c Ω), hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) Ω z C z' → ∃ (C₀ : hkKer (Xo := Xo) P p i Ω w) (w' : FrPt Xo c Ω), hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) Ω w C₀ w' ∧ FrBor t w' z' := by
  first | exact @GlobalTheory.HeckeBorelChange.hkRelFr_frBor | exact GlobalTheory.HeckeBorelChange.hkRelFr_frBor | (intros; apply GlobalTheory.HeckeBorelChange.hkRelFr_frBor <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCDVRFractionFieldReadingInCpFiniteExtensionStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Pj GlobalTheory.GeoTie GlobalTheory.GoodPts

theorem _root_.GlobalTheory.T.isCDVRFractionFieldReadingInCp_finite_extension : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p]) (T : CDVR) (io : F →+* T.Fr) (k : T.Fr →+* ℂ_[p]), IsReading φ T io k → ∀ (T' : CDVR) (i : T.Fr →+* T'.Fr), GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsFinExt T T' i → ∀ j : T'.Fr →+* ℂ_[p], j.comp i = k → IsReading φ T' (i.comp io) j := by
  first | exact @GlobalTheory.GeoTie.ReadExt.isReading_ext | exact GlobalTheory.GeoTie.ReadExt.isReading_ext | (intros; apply GlobalTheory.GeoTie.ReadExt.isReading_ext <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeQuotientIntegralFramedPointCompleteField

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HeckeStableAt

theorem heckeStable : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type)
    (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL]
    (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw)
    (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1))
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw)
    (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]),
    (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) →
    ∀ (b : Bool) (j : Fin D.R.m), HeckeStable YS iC b j := by
  intro hI D Γ _ _ Pl0 I0 T1 A3 T0 _ Rl cG S YS κ v₀ fw i iC _ b j k P hk z C
  obtain ⟨hHP, hne⟩ := GlobalTheory.T.isSplitHeckePrimeOffLevel_of_heckeIndexPlace D T0 fw.laws i k P hk
  have hP' := GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff.2 hHP
  obtain ⟨z', hz'⟩ := GlobalTheory.HeckePointLaw.heckePointLaws.2.1 D.host.E T0.Q.H (T0.Q.Dw ((j : ℕ) + 1)) T0.Q.l
    (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c P.asIdeal (charAt P) k hP' (PAt (embC YS iC b)) z.1 C
  obtain ⟨T, io, kk, h, y, u, hy, hu, w, hw, hb⟩ := z.2
  obtain ⟨C₀, w', hw', hb'⟩ := GlobalTheory.T.heckeQuotient_frame_change_of_triangular_frame_change _ _ _ _ _ _ P.asIdeal (charAt P) k hHP _ u w z.1 hb C z' hz'
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_ramification_overPlace_of_cdvrReadingInCp (D.ntw.l i) T0.Q.c.F (embC YS iC b) T io kk h
  have hpla : ((charAt P : ℕ) : 𝓞 T0.Q.c.F) ∉ (placeAt (embC YS iC b)).asIdeal := by
    intro hm
    have hl := natCast_mem_placeAt (embC YS iC b)
    have hcop : Nat.Coprime (charAt P) (D.ntw.l i) :=
      (Nat.coprime_primes (charAt_prime P) (Fact.out : (D.ntw.l i).Prime)).2 hne
    obtain ⟨a, c, hac⟩ : IsCoprime ((charAt P : ℕ) : 𝓞 T0.Q.c.F) ((D.ntw.l i : ℕ) : 𝓞 T0.Q.c.F) :=
      Nat.Coprime.cast hcop
    exact (placeAt (embC YS iC b)).isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hac ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm) (Ideal.mul_mem_left _ _ hl)))
  letI := io.toAlgebra
  have hint := GlobalTheory.T.heckePoint_integral_upToUnits_anyAlgClosedField hI D.host.E T0.Q.H (T0.Q.Dw ((j : ℕ) + 1)) T0.Q.l (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c
    (placeAt (embC YS iC b)) P.asIdeal (charAt P) k hHP hpla T io e he y hy (PAt (embC YS iC b)) h.alg w hw C₀ w' hw'
  obtain ⟨T', i', hi', j', hj', y', hy', -, w2, u2, hw2, hb2⟩ := hint
  letI := (i'.comp io).toAlgebra
  let jj : T'.Fr →+* ℂ_[D.ntw.l i] := (toCp (embC YS iC b)).comp j'.toRingHom
  have hjj : jj.comp i' = kk := RingHom.ext fun a => congrArg (toCp (embC YS iC b)) (DFunLike.congr_fun hj' a)
  have hR := GlobalTheory.T.isCDVRFractionFieldReadingInCp_finite_extension (D.ntw.l i) T0.Q.c.F (embC YS iC b) T io kk h T' i' hi' jj hjj
  have hRa : hR.alg = j' := AlgHom.ext fun _ => rfl
  let u2' : Ix (T0.Q.Dw ((j : ℕ) + 1)) → (PAt (embC YS iC b))ˣ :=
    fun a => Units.map (j'.toRingHom.comp (algebraMap T'.V T'.Fr)).toMonoidHom (u2 a)
  have hbor := (GlobalTheory.Frames.frBor_calculus _ _ _ _ _ _ _ w2 w' z').2.2.1 u2' u hb2 hb'
  have hunit : ∀ a, ‖toCp (embC YS iC b) (u2' a)‖ = 1 := fun a => by
    have h1 : ‖jj (algebraMap T'.V T'.Fr (u2 a : T'.V))‖ ≤ 1 := (hR.int _).2 ⟨_, rfl⟩
    have h2 : ‖jj (algebraMap T'.V T'.Fr ((u2 a)⁻¹ : T'.Vˣ))‖ ≤ 1 := (hR.int _).2 ⟨_, rfl⟩
    have h3 : jj (algebraMap T'.V T'.Fr (u2 a : T'.V)) * jj (algebraMap T'.V T'.Fr ((u2 a)⁻¹ : T'.Vˣ)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    have h4 := congrArg norm h3
    rw [norm_mul, norm_one] at h4
    have h5 : ‖jj (algebraMap T'.V T'.Fr (u2 a : T'.V))‖ = 1 := by
      refine le_antisymm h1 (by_contra fun hlt => ?_)
      push_neg at hlt
      have : ‖jj (algebraMap T'.V T'.Fr (u2 a : T'.V))‖ * ‖jj (algebraMap T'.V T'.Fr ((u2 a)⁻¹ : T'.Vˣ))‖ < 1 :=
        (mul_le_of_le_one_right (norm_nonneg _) h2).trans_lt hlt
      exact this.ne h4
    exact h5
  have hnorm : ∀ a, ‖toCp (embC YS iC b) ((u * u2') a)‖ = 1 := fun a => by
    rw [Pi.mul_apply, Units.val_mul, map_mul, norm_mul, hu a, hunit a, one_mul]
  refine ⟨⟨z', T', i'.comp io, jj, hR, y', u * u2', hy', hnorm, w2, hRa ▸ hw2, hbor⟩, hz'⟩

end GlobalTheory.HeckeStableAt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeQuotientIntegralFramedPointCompleteFieldStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie

theorem _root_.GlobalTheory.T.heckeQuotient_integral_framed_point_complete_field : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), HeckeStable YS iC b j := by
  first | exact @GlobalTheory.HeckeStableAt.heckeStable | exact GlobalTheory.HeckeStableAt.heckeStable | (intros; apply GlobalTheory.HeckeStableAt.heckeStable <;> assumption)
end
end
