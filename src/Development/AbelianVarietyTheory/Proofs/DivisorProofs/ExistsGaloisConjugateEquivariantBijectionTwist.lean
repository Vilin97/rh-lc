module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecTw
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricFramePullbackMumfordFrameGaloisTwistStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OperatorRelationPullbackGaloisAutomorphismStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaFamilyGaloisTwistBijective
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaFamilyGaloisTwistFixesIntegralFamilStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaSectionsGaloisTwistBijectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaSectionsGaloisTwistChartSemilinearStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaSectionsGaloisTwistIsConjugateStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtPull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupActionPullbackThetaSectionsGaloisTwistStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UwRQeIsNsmul

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaFamilyGaloisTwistBijectiveStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

theorem _root_.GlobalTheory.T.pullbackThetaFamilyGaloisTwist_bijective : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R), Function.Bijective (famTw D N σ) := by
  first | exact @GlobalTheory.Mum.Conj.FamBij.famTw_bijective | exact GlobalTheory.Mum.Conj.FamBij.famTw_bijective | (intros; apply GlobalTheory.Mum.Conj.FamBij.famTw_bijective <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaFamilyGaloisTwistChartAdd

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

noncomputable section

namespace GlobalTheory.Mum.Conj

theorem famTw_add_f : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (s s' s'' : Fam D (Kb R) N), (∀ α j, (s''.s α).f j = (s.s α).f j + (s'.s α).f j) → ∀ α j, ((famTw D N σ s'').s α).f j = ((famTw D N σ s).s α).f j + ((famTw D N σ s').s α).f j := by
  intro R _ _ D N σ s s' s'' h α j
  have e : s'' = s + s' := ReciprocityTheory.ChartRestriction.G.DVR.fam_ext fun α j => (h α j).trans (ReciprocityTheory.ChartRestriction.G.DVR.add_f s s' α j).symm
  subst e
  show ((GlobalTheory.FieldBaseChange.famPull D (Kb R) (TwF σ) GlobalTheory.allSixLaws.1.globalFns N (s + s') :
    Fam D (TwF σ) N).s α).f j = _
  rw [map_add (f := _)]
  rfl

end GlobalTheory.Mum.Conj
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaFamilyGaloisTwistChartAddStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

theorem _root_.GlobalTheory.T.pullbackThetaFamilyGaloisTwist_chart_add : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (s s' s'' : Fam D (Kb R) N), (∀ α j, (s''.s α).f j = (s.s α).f j + (s'.s α).f j) → ∀ α j, ((famTw D N σ s'').s α).f j = ((famTw D N σ s).s α).f j + ((famTw D N σ s').s α).f j := by
  first | exact @GlobalTheory.Mum.Conj.famTw_add_f | exact GlobalTheory.Mum.Conj.famTw_add_f | (intros; apply GlobalTheory.Mum.Conj.famTw_add_f <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaFamilyGaloisTwistSemilinearSmul

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

theorem famTw_isSmul : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ)
    (σ : Kb R →ₐ[FractionRing R] Kb R) (c : Kb R) (s s' : Fam D (Kb R) N),
    Fam.IsSmul D (Kb R) c s s' → Fam.IsSmul D (Kb R) (σ c) (famTw D N σ s) (famTw D N σ s') := by
  intro R _ _ D N σ c s s' h
  rw [ReciprocityTheory.ChartRestriction.G.DVR.isSmul_iff] at h
  subst h
  intro α j
  have e := map_smulₛₗ (GlobalTheory.FieldBaseChange.famPull D (Kb R) (TwF σ) GlobalTheory.allSixLaws.1.globalFns N) c s
  exact congrArg (fun q : Fam D (TwF σ) N => (q.s α).f j) e

end GlobalTheory.Mum.Conj
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaFamilyGaloisTwistSemilinearSmulStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

theorem _root_.GlobalTheory.T.pullbackThetaFamilyGaloisTwist_semilinear_smul : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (c : Kb R) (s s' : Fam D (Kb R) N), Fam.IsSmul D (Kb R) c s s' → Fam.IsSmul D (Kb R) (σ c) (famTw D N σ s) (famTw D N σ s') := by
  first | exact @GlobalTheory.Mum.Conj.famTw_isSmul | exact GlobalTheory.Mum.Conj.famTw_isSmul | (intros; apply GlobalTheory.Mum.Conj.famTw_isSmul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaSectionsGaloisTwistChartAdd

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

theorem secTw_add_chart : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ)
    (σ : Kb R →ₐ[FractionRing R] Kb R) (t t' t'' : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N),
    (∀ j, t''.f j = t.f j + t'.f j) → ∀ j, (secTw A N σ t'').f j = (secTw A N σ t).f j + (secTw A N σ t').f j := by
  intro R _ _ A N σ t t' t'' h j
  show GlobalTheory.FieldBaseChange.pullFn _ _ (t''.f j) =
    GlobalTheory.FieldBaseChange.pullFn _ _ (t.f j) + GlobalTheory.FieldBaseChange.pullFn _ _ (t'.f j)
  rw [h j]
  exact map_add _ _ _

end GlobalTheory.Mum.Conj
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaSectionsGaloisTwistChartAddStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

theorem _root_.GlobalTheory.T.pullbackThetaSectionsGaloisTwist_chart_add : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (t t' t'' : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N), (∀ j, t''.f j = t.f j + t'.f j) → ∀ j, (secTw A N σ t'').f j = (secTw A N σ t).f j + (secTw A N σ t').f j := by
  first | exact @GlobalTheory.Mum.Conj.secTw_add_chart | exact GlobalTheory.Mum.Conj.secTw_add_chart | (intros; apply GlobalTheory.Mum.Conj.secTw_add_chart <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLiftGaloisTwistOfConjugatePoint

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

theorem symLift_thTw : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ) (τ : Kb R →ₐ[FractionRing R] Kb R) (x x' : TFK (R := R) (Kb R) ⟶ A.A) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) (Kb R))), SymLift A.A A.L N N x θ → x'.left = spMap τ.toRingHom ≫ x.left → SymLift A.A A.L N N x' (thTw A N τ θ) := by
  intro R _ _ A N τ x x' θ h hx
  have ex : x' = twK τ ≫ x := Over.OverMorphism.ext (by rw [hx, Over.comp_left, twK_left])
  subst ex
  have eM : mTw A τ = twK τ ▷ A.A := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [mTw_fst, whiskerRight_fst]
    · rw [mTw_snd, whiskerRight_snd]
  exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.symLift_pull A.isLB (twK τ) h _ (thTw A N τ θ).isGen fun r z J hJ => by
    show val (genCast _ _) r z J = _
    rw [val_genCast]
    exact (val_pull hJ _ _ r).trans (by rw [eM])

end GlobalTheory.Mum.Conj
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLiftGaloisTwistOfConjugatePointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

theorem _root_.GlobalTheory.T.symmetricLift_galoisTwist_of_conjugatePoint : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ) (τ : Kb R →ₐ[FractionRing R] Kb R) (x x' : TFK (R := R) (Kb R) ⟶ A.A) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) (Kb R))), SymLift A.A A.L N N x θ → x'.left = spMap τ.toRingHom ≫ x.left → SymLift A.A A.L N N x' (thTw A N τ θ) := by
  first | exact @GlobalTheory.Mum.Conj.symLift_thTw | exact GlobalTheory.Mum.Conj.symLift_thTw | (intros; apply GlobalTheory.Mum.Conj.symLift_thTw <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisConjugateEquivariantBijectionTwist

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


open GlobalTheory.Mum GlobalTheory.Mum.Conj in
theorem GlobalTheory.Mum.exists_eqv_conj : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) E, Eqv D.toPre A (Kb R) N lab E → (∀ τ : Kb R →ₐ[FractionRing R] Kb R, LabExt τ lab lab) → ∀ σ : Kb R →ₐ[FractionRing R] Kb R, ∃ E', Eqv D.toPre A (Kb R) N lab E' ∧ ∀ (F₀ : IntFam (maximalIdeal R) D.toPre N) s, F₀.Over s → SecTw σ (E s) (E' s) := by
  intro R _ _ _ _ D A N _ lab E hE hlab σ
  have hσ : Function.Bijective σ := Algebra.IsAlgebraic.algHom_bijective σ
  let σe : Kb R ≃ₐ[FractionRing R] Kb R := AlgEquiv.ofBijective σ hσ
  let τ : Kb R →ₐ[FractionRing R] Kb R := σe.symm.toAlgHom
  have hστ : σ.comp τ = AlgHom.id _ _ := AlgHom.ext fun x => σe.apply_symm_apply x
  have hστ' : ∀ x, σ (τ x) = x := fun x => σe.apply_symm_apply x
  refine ⟨fun s => secTw A N σ (E (famTw D.toPre N τ s)), ⟨?_, ?_, ?_, hE.onto, hE.frame, hE.lift, ?_⟩, ?_⟩
  · exact (GlobalTheory.T.pullbackThetaSectionsGaloisTwist_bijective R A N σ).comp (hE.bij.comp (GlobalTheory.T.pullbackThetaFamilyGaloisTwist_bijective R D.toPre N τ))
  · intro s s' s'' h j
    exact GlobalTheory.T.pullbackThetaSectionsGaloisTwist_chart_add R A N σ _ _ _ (hE.add _ _ _ (GlobalTheory.T.pullbackThetaFamilyGaloisTwist_chart_add R D.toPre N τ _ _ _ h)) j
  · intro c s s' h j
    have := GlobalTheory.T.pullbackThetaSectionsGaloisTwist_chart_semilinear R A N σ (τ c) _ _ (hE.smul (τ c) _ _ (GlobalTheory.T.pullbackThetaFamilyGaloisTwist_semilinear_smul R D.toPre N τ c _ _ h)) j
    rwa [hστ'] at this
  · intro p w θ s s' hw hθ hφ
    obtain ⟨p₀, hp₀⟩ := qkExtExists R D.toPre (Kb R) (Kb R) τ.toRingHom (fun r => τ.commutes r) N p
    have hx := hlab τ p p₀ hp₀
    exact GlobalTheory.T.thetaGroupAction_pullbackThetaSectionsGaloisTwist R A N σ τ hστ θ _ _ (hE.act p₀ (frTw D.toPre τ hp₀ w) (thTw A N τ θ) _ _
      (GlobalTheory.T.isSymmetricFrame_pullbackMumfordFrameGaloisTwist R D.toPre N τ p p₀ hp₀ w hw) (GlobalTheory.T.symmetricLift_galoisTwist_of_conjugatePoint R A N τ _ _ θ hθ hx) (GlobalTheory.T.operator_relation_pullback_galois_automorphism R D.toPre N τ p p₀ hp₀ w s s' hφ))
  · intro F₀ s hs
    show SecTw σ (E s) (secTw A N σ (E (famTw D.toPre N τ s)))
    rw [GlobalTheory.T.pullbackThetaFamilyGaloisTwist_fixes_integralFamily R _ D.toPre N τ F₀ s hs]
    exact GlobalTheory.T.pullbackThetaSectionsGaloisTwist_isConjugate R A N σ (E s)
end
end
