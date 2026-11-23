module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AnalyticDictionaryExpAdditiveSurjectiveLinear
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AnalyticDictionaryExpHolomorphicOverUnif
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AnalyticDictionaryExpKernelIotaTorusPoints
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLevelOneSectionEqKappaThetaStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqSpMapOfInjective
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsLatticeVectorRepAndShift
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
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExponentialFamilyDerivSumsAtPeriodStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AnalyticDictionaryExpKernelIotaTorusPointsStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SmulPeriodMapMkZeroFstEqNegForm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MemThetaShiftZero
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsLatticeVectorRepAndShiftStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.exists_latticeVector_rep_and_shift : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a) (k : ℕ), 1 ≤ k → (∀ p, ∃ la, Λ.Rep k p la) ∧ ∀ p la e, Λ.Rep k p la → ∃ q : Out.QkPt a.D₀ ℂ k, q.y = Λ.ε (la + k • e).y ∧ q.g = Λ.ex0 ((k : ℂ)⁻¹ • Λ.A.P0 (la + k • e)) ∧ ∀ q', QkExt (algebraMap _ ℂ) p q' → Out.QkPt.Equiv a.D₀ ℂ q q' := by
  first | exact @GlobalTheory.GtRep.exists_rep_and_shift | exact GlobalTheory.GtRep.exists_rep_and_shift | (intros; apply GlobalTheory.GtRep.exists_rep_and_shift <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtAnOrthKerIff

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts

theorem gtAn_orth_ker_iff : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a) (v : Λ.A.La), (∀ v' : Λ.A.La, Λ.ε v'.y = 0 → Λ.A.EF v v' = 0) ↔ (Λ.ε v.y = 0 ∧ ∀ s : ℂ, ∃ x, IsTorusPt (Λ.ex0 (s • Λ.A.P0 v)) x ∧ ∀ v' : Λ.A.La, x (Λ.ε v'.y) = eTwoPi (-(s * Λ.A.EF v v'))) := by
  intro _ _ E _ _ _ H _ D l c O _ β _ _ b a Λ v
  obtain ⟨-, -, htor, hlam⟩ := GlobalTheory.T.analyticDictionaryExp_kernel_iota_torusPoints E H D l c O β b a Λ
  have hε : ∀ x : Λ.A.X, Λ.ε x = 0 ↔ x = 0 := fun x => map_eq_zero_iff _ Λ.ε.injective
  simp only [hε]
  constructor
  · intro h
    refine ⟨((Λ.A.orth_ker_iff v).1 h).1, fun s => ?_⟩
    obtain ⟨h2, h1⟩ := Λ.A.smul_periodMap_of_orthogonal_ker h s
    have hz : s • Λ.A.P0 v = ((s • Λ.A.P0 v).1, 0) := Prod.ext rfl h2
    refine ⟨fun x => eTwoPi ((s • Λ.A.P0 v).1 (Λ.ε.symm x)), ?_, fun v' => ?_⟩
    · have := htor (s • Λ.A.P0 v).1
      rwa [← hz] at this
    · have h3 : Λ.ε.symm (Λ.ε v'.y) = v'.y := Λ.ε.symm_apply_apply _
      simp only [h3, h1]
  · rintro ⟨hv, h⟩
    refine (Λ.A.orth_ker_iff_forall_smul_mem v).2 ⟨hv, fun s => ?_⟩
    obtain ⟨x, hx, -⟩ := h s
    exact hlam _ x hx

end GlobalTheory.ArcPts
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsHolToCompClm

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts

theorem isHolTo_comp_clm {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V']
    [NormedSpace ℂ V'] {X : Scheme.{0}} {y : V → (Sp ℂ ⟶ X)} (hy : IsHolTo Set.univ y) (φ : V' →L[ℂ] V) :
    IsHolTo Set.univ (fun z => y (φ z)) := by
  intro U f
  obtain ⟨h1, h2⟩ := hy U f
  exact ⟨h1.preimage φ.continuous, h2.comp φ.differentiable.differentiableOn fun _ hz => hz⟩

theorem nonempty_holArc : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (C : Chain W Λ) (Γ : Germs) (Ψ : SpecPts C.Φ Γ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (bF.comp (IntermediateField.inclusion c.le).toRingHom) ty) (laA laM : D.La → Λ.A.La) (K : Cmp Fu Λ.A Ψ.yw Ψ.pi laA laM), C.Φ.Rational → (∀ v, Λ.Rep l.A (a.etaA v) (laA v)) → (∀ v, Λ.Rep l.M (a.eta v) (laM v)) → ∀ lin cst (T₁ : ℝ), (∀ w : ℂ, T₁ < w.im → IsFibAt Λ.A Xo.univ.t lin cst w (Ψ.yw w) (Ψ.pi w) (Ψ.fr w)) → Nonempty (HolArc Y bF a χ W Fu) := by
  intro hL hL2 E _ _ _ H _ D l Xo c O _ β Y _ _ bF a χ W Λ C Γ Ψ g ty Fu laA laM K hrat hA hM lin cst T₁ hfib
  obtain ⟨hadd, honto, hlin⟩ := ex0_additive_surjective_equivariant hL hL2 E H D l c O β _ a Λ
  obtain ⟨hb, hchi⟩ := analyticDictionaryExp_holomorphic_over_unif E H D l c O β _ a Λ
  obtain ⟨hker, hiota, htor, -⟩ := GtKer.ker_iota_torus E H D l c O β _ a Λ
  have hfin : AnFin Λ.A := (ArcThetaSpaces.sections_theta hL hL2 E H D l c O β _ a Λ).2.1
  have hrie := gtAn_orth_ker_iff hL hL2 E H D l c O β _ a Λ
  have hpt := ArcPoint.point_sumsAt E H D l Xo c O β Y bF a χ W Λ C Γ Ψ g ty Fu laA laM K
  have hdiff := GlobalTheory.T.exponentialFamily_deriv_sumsAt_period hL hL2 E H D l Xo c O β Y bF a χ W Λ C Γ Ψ g ty Fu laA laM K hfin hrat
  obtain ⟨T₂, hth⟩ := GlobalTheory.T.arc_levelOne_section_eq_kappa_theta hL hL2 E H D l Xo c O β Y bF a χ W Λ C Γ Ψ g ty Fu laA laM K hfin lin cst T₁ hfib
  have hrep := GlobalTheory.T.exists_latticeVector_rep_and_shift hL hL2 E H D l c O β _ a Λ
  have hsm : ∀ (s : ℂ) (v : Λ.A.V), K.h.symm (s • K.h v) = s • v := fun s v => by
    rw [map_smul, K.h.symm_apply_apply]
  refine ⟨{
    i := K.i
    T := max K.T T₂
    P₀ := (K.h.toLinearEquiv.toAddEquiv.toAddMonoidHom.comp Λ.A.P0).comp K.gam.toAddEquiv.toAddMonoidHom
    N := (K.h.toLinearEquiv.toAddEquiv.toAddMonoidHom.comp Λ.A.N).comp K.gam.toAddEquiv.toAddMonoidHom
    Pw := K.Pw
    Pw_eq := fun w v => ?_
    y := Λ.ε.toLinearMap ∘ₗ Λ.A.yLin ∘ₗ K.gam.toLinearMap
    y_onto := Λ.ε.surjective.comp (Λ.A.yLin_surjective.comp K.gam.surjective)
    ex₀ := fun z => Λ.ex0 (K.h.symm z)
    period := fun w hw => K.period w (lt_of_le_of_lt (le_max_left _ _) hw)
    add := fun z z' => ?_
    onto := honto.comp K.h.symm.surjective
    lin := fun x z => ?_
    hol_b := isHolTo_comp_clm hb (K.h.symm : (Fin g → ℂ) →L[ℂ] Λ.A.V)
    hol_chi := fun x j => (hchi x j).1.comp K.h.symm.differentiable.differentiableOn fun _ hz => hz
    ker := fun z => ?_
    iota := fun v => ?_
    shift := fun w v => ?_
    levelA := fun v => ?_
    levelM := fun v hv => ?_
    riemann := fun v => ?_
    point := hpt
    diff := fun z₀ ν v V f h1 h2 h3 => hdiff z₀ ν v V f ⟨h1, h2, h3⟩
    theta := fun th σ fam bas S h τ c₁ c₂ w₂ w₁ w₀ h1 h2 h3 =>
      hth _ (le_max_right _ _) th σ fam bas S h τ c₁ c₂ w₂ w₁ w₀ ⟨h1, h2, h3⟩ }⟩
  · show K.Pw w v = K.h (Λ.A.P0 (K.gam v)) + w • K.h (Λ.A.N (K.gam v))
    rw [K.Pw_eq, AnArc.Pw_apply, map_add (f := _), map_smul]
  · rw [map_add (f := _)]; exact hadd _ _
  · have : K.h.symm (fun k => ty k (x : E) * z k) = Λ.A.actV x (K.h.symm z) := by
      apply K.h.injective
      funext k
      rw [K.h_act, K.h.apply_symm_apply, K.h.apply_symm_apply]
    rw [this]
    exact hlin x _
  · refine (hker _).trans ⟨?_, ?_⟩
    · rintro ⟨la, h0, hz⟩
      obtain ⟨v, rfl⟩ := K.gam.surjective la
      refine ⟨v, ?_, ?_⟩
      · show Λ.ε (K.gam v).y = 0
        rw [h0, map_zero]
      · show z = K.h (Λ.A.P0 (K.gam v))
        rw [← hz, K.h.apply_symm_apply]
    · rintro ⟨v, h0, hz⟩
      refine ⟨K.gam v, (map_eq_zero_iff _ Λ.ε.injective).1 h0, ?_⟩
      rw [hz]
      exact K.h.symm_apply_apply _
  · show Out.GtPtF.IsIota (Λ.ε (K.gam v).y) (Λ.ex0 (K.h.symm (K.h (Λ.A.P0 (K.gam v)))))
    rw [K.h.symm_apply_apply]
    exact hiota _
  · show IsTorusPt (Λ.ex0 (K.h.symm (w • K.h (Λ.A.N (K.gam v))))) (fun x => eTwoPi (w * a.be (Λ.ε (K.gam v).y) x))
    have h1 : w • Λ.A.N (K.gam v) = ((w • Λ.A.N (K.gam v)).1, 0) := Prod.ext rfl (by simp [AnArc.N])
    rw [hsm, h1]
    convert htor (w • Λ.A.N (K.gam v)).1 using 3 with x
    show _ = w * ((Λ.A.be (K.gam v).y (Λ.ε.symm x) : ℤ) : ℂ)
    rw [Λ.be_eq, Λ.ε.apply_symm_apply]
  · obtain ⟨e, he⟩ := K.levA v
    obtain ⟨q, h1, h2, h3⟩ := (hrep l.A l.A_pos).2 _ _ e (hA v)
    rw [← he] at h1 h2
    exact ⟨q, h1, h2.trans (congrArg Λ.ex0 (hsm _ _).symm), h3⟩
  · obtain ⟨e, he⟩ := K.levM v hv
    obtain ⟨q, h1, h2, h3⟩ := (hrep l.M (le_trans (by norm_num) l.three_le)).2 _ _ e (hM v)
    rw [← he] at h1 h2
    exact ⟨q, h1, h2.trans (congrArg Λ.ex0 (hsm _ _).symm), h3⟩
  · show (∀ v', Λ.ε (K.gam v').y = 0 → (Fu.Di K.i).EF v v' = 0) ↔ (Λ.ε (K.gam v).y = 0 ∧ ∀ s : ℂ, ∃ x,
      IsTorusPt (Λ.ex0 (K.h.symm (s • K.h (Λ.A.P0 (K.gam v))))) x ∧
        ∀ v', x (Λ.ε (K.gam v').y) = eTwoPi (-(s * (Fu.Di K.i).EF v v')))
    simp only [hsm, ← K.EF_eq]
    have := hrie (K.gam v)
    simp only [K.gam.surjective.forall] at this
    exact this

end GlobalTheory.ArcPts
end
end
