module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalDomainPrime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationDataPullbackInjectiveLocalHom
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionGaloisEquivariantLabels
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeometricFibreIsoOfTraitUniformisationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionLabelsUniformisedDominatingTraitStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniTrait
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedTraitDescentFiniteExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordUniformisationUnitaryTypeTraitStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionLabelsFiniteExtensionGaloisEquivariStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedCoverFiniteExtOfSymmetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegCompOfInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLabelledCoverOfOddPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PelOKOfIsPullDeg

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionGaloisEquivariantLabelsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_finite_extension_galois_equivariant_labels : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))) (lab : Labels D₁.toPre A), FinExt ρ → Nonempty (IsPullDeg ρ D.toPre D₁.toPre) → (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) → OneTrait D₁.toPre A lab → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ₂ : R →+* R₂) (D₂ : DegData R₂ (maximalIdeal R₂)) (A₂ : PolAV (Sp (FractionRing R₂))) (lab₂ : Labels D₂.toPre A₂), FinExt ρ₂ ∧ Nonempty (IsPullDeg ρ₂ D.toPre D₂.toPre) ∧ (letI := A₂.isAb.comm; GlobalTheory.ZH.HypS A₂.A A₂.L) ∧ OneTrait D₂.toPre A₂ lab₂ ∧ GalEqN n lab₂ := by
  first | exact @GlobalTheory.Mum.exists_finExt_galEqN | exact GlobalTheory.Mum.exists_finExt_galEqN | (intros; apply GlobalTheory.Mum.exists_finExt_galEqN <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedTraitDescentFiniteExtStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_uniformisedTrait_descent_finite_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (D' : DegData W (maximalIdeal W)) (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (A' : PolAV (Sp (FractionRing W))), Nonempty (IsPullDeg φ D.toPre D'.toPre) → IsSemiAbelian G' → Nonempty (Unif (maximalIdeal W) D' A' G') → (letI := A'.isAb.comm; GlobalTheory.ZH.HypS A'.A A'.L) → ∀ (A₀ : PolAV (Sp (Kb R))) (e₀ : Kb R →+* Kb W), (∀ r, e₀ (algebraMap (FractionRing R) (Kb R) (algebraMap R _ r)) = algebraMap (FractionRing W) (Kb W) (algebraMap W _ (φ r))) → (letI := A₀.isAb.comm; GlobalTheory.ZH.HypS A₀.A A₀.L) → GeomIso A₀ A' e₀ (algebraMap (FractionRing W) (Kb W)) → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) ∧ UniTrait D₁.toPre A := by
  first | exact @GlobalTheory.Mum.ClosureDescent.exists_uniTrait | exact GlobalTheory.Mum.ClosureDescent.exists_uniTrait | (intros; apply GlobalTheory.Mum.ClosureDescent.exists_uniTrait <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelledSemiAbelianCoverFiniteExtension

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_desc_labels : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (D' : DegData W (maximalIdeal W)) (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (A' : PolAV (Sp (FractionRing W))), Nonempty (IsPullDeg φ D.toPre D'.toPre) → IsSemiAbelian G' → Nonempty (Unif (maximalIdeal W) D' A' G') → (letI := A'.isAb.comm; GlobalTheory.ZH.HypS A'.A A'.L) → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))) (lab : Labels D₁.toPre A), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) ∧ OneTrait D₁.toPre A lab ∧ GalEqN n lab := by
  intro R _ _ _ hR D n hn ho hu W _ _ _ hW φ hφ hl D' G' _ _ A' hP hG hU hS
  obtain ⟨A₀, e₀, hc, hS₀, hI⟩ := GlobalTheory.T.exists_geometricFibreIso_of_traitUniformisation R hR D n hn ho hu W hW φ hφ hl D' G' A' hP hG hU hS
  obtain ⟨R₁, _, _, _, ρ, D₁, A, hF, hP₁, hS₁, hT⟩ :=
    GlobalTheory.T.exists_uniformisedTrait_descent_finite_ext R hR D n hn ho hu W hW φ hφ hl D' G' A' hP hG hU hS A₀ e₀ hc hS₀ hI
  have hR₁ : Base R₁ := ⟨hF.1, by haveI := hR.2; exact charZero_of_injective_ringHom hF.2.1⟩
  obtain ⟨lab, hO⟩ := GlobalTheory.T.exists_torsionLabels_uniformisedDominatingTrait R₁ hR₁ D₁ A hT
  exact GlobalTheory.T.exists_finite_extension_galois_equivariant_labels R hR D n hn ho hu R₁ ρ D₁ A lab hF hP₁ hS₁ hO

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelledSemiAbelianCoverFiniteExtensionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_labelledSemiAbelianCover_finite_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (D' : DegData W (maximalIdeal W)) (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (A' : PolAV (Sp (FractionRing W))), Nonempty (IsPullDeg φ D.toPre D'.toPre) → IsSemiAbelian G' → Nonempty (Unif (maximalIdeal W) D' A' G') → (letI := A'.isAb.comm; GlobalTheory.ZH.HypS A'.A A'.L) → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))) (lab : Labels D₁.toPre A), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) ∧ OneTrait D₁.toPre A lab ∧ GalEqN n lab := by
  first | exact @GlobalTheory.Mum.exists_desc_labels | exact GlobalTheory.Mum.exists_desc_labels | (intros; apply GlobalTheory.Mum.exists_desc_labels <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelledCoverUnitaryPELTypeFiniteExt

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_odd_prime_isUnit_in_localRing (R : Type) [CommRing R] [IsLocalRing R] :
    ∃ n : ℕ, n.Prime ∧ Odd n ∧ IsUnit (n : R) := by
  have h : IsUnit ((2 : R) * (3 : ℕ) + (-1) * (5 : ℕ)) := by
    have : (2 : R) * (3 : ℕ) + (-1) * (5 : ℕ) = 1 := by push_cast; ring
    rw [this]; exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h with h | h
  · exact ⟨3, Nat.prime_three, by decide, isUnit_of_mul_isUnit_right h⟩
  · exact ⟨5, Nat.prime_five, by decide, isUnit_of_mul_isUnit_right h⟩

theorem exists_labCover_of_pelOK : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (D : DegData R (maximalIdeal R)) [Module (𝓞 E) D.toPre.X] (o : letI := H.starRing; D.toPre.OAct (𝓞 E)), Nontrivial D.toPre.X → PelOK Dm D.toPre o → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D' : DegData R' (maximalIdeal R')), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D'.toPre) ∧ Nonempty (LabCover D') := by
  intro R _ _ _ hR E _ _ _ H Dm D _ o hX hP
  have := hR.1.1
  have := hR.2
  obtain ⟨n, hn, ho, hu⟩ := exists_odd_prime_isUnit_in_localRing R
  obtain ⟨V, _, _, _, φ, hV, hφ, hc⟩ := GlobalTheory.PrimeUnif.exists_cdvr R (maximalIdeal R)
  have hloc : IsLocalHom φ := ⟨fun a ha => by
    by_contra hna
    have h1 : a ∈ (maximalIdeal V).comap φ := by rw [hc]; exact hna
    exact h1 ha⟩
  obtain ⟨DV, ⟨hDV⟩⟩ := GlobalTheory.MumPull.exists_pull R V φ hφ hloc D
  obtain ⟨_, oV, hPV⟩ := GlobalTheory.Mum.pelOK_of_isPullDeg R hR E H Dm D o hP V φ hφ DV ⟨hDV⟩
  have hXV : Nontrivial DV.toPre.X := hDV.xe.toEquiv.nontrivial
  obtain ⟨V', _, _, _, io, D', G', _, _, A', hV', hio, hfin, hD', hG', hU', hS'⟩ := GlobalTheory.T.exists_mumfordUniformisation_unitaryTypeTrait V hV E H Dm DV oV hXV hPV
  have hioloc : IsLocalHom io := hfin.to_isIntegral.isLocalHom hio
  obtain ⟨R₁, _, _, _, ρ₁, D₁, A, lab, hf₁, hD₁, hS, h1, h2⟩ := GlobalTheory.T.exists_labelledSemiAbelianCover_finite_extension R hR D n hn ho hu V' hV' (io.comp φ)
    (hio.comp hφ) inferInstance D' G' A'
    (GlobalTheory.Mum.nonempty_isPullDeg_comp_of_injective R V V' φ io _ _ _ hio ⟨hDV⟩ hD') hG' hU' hS'
  have hR₁ : Base R₁ := ⟨hf₁.1, charZero_of_injective_ringHom hf₁.2.1⟩
  have := hR₁.2
  obtain ⟨R₂, _, _, _, ρ₂, C, a, hf₂, hfib⟩ := GlobalTheory.T.exists_uniformised_cover_finite_ext_of_symmetric R₁ hR₁ A hS
  have hR₂ : Base R₂ := ⟨hf₂.1, charZero_of_injective_ringHom hf₂.2.1⟩
  obtain ⟨D₂, hD₂⟩ := GlobalTheory.MumPull.exists_pull R₁ R₂ ρ₂ hf₂.2.1 (hf₂.2.2.to_isIntegral.isLocalHom hf₂.2.1) D₁
  obtain ⟨lab₂, k1, k2⟩ := GlobalTheory.T.exists_torsionLabels_finiteExtension_galoisEquivariant R₁ hR₁ D₁ A lab n h1 h2 R₂ ρ₂ hf₂ D₂ hD₂ C.A a hfib hn.pos
  have hu₂ : IsUnit (n : R₂) := by simpa using hu.map (ρ₂.comp ρ₁)
  exact ⟨R₂, _, _, _, ρ₂.comp ρ₁, D₂, ⟨hf₂.1, hf₂.2.1.comp hf₁.2.1, hf₂.2.2.comp hf₁.2.2⟩,
    GlobalTheory.Mum.nonempty_isPullDeg_comp_of_injective R R₁ R₂ ρ₁ ρ₂ _ _ _ hf₂.2.1 hD₁ hD₂,
    GlobalTheory.T.nonempty_labelled_cover_of_odd_prime R₂ hR₂ D₂ C lab₂ n hn ho hu₂ k1 k2⟩

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelledCoverUnitaryPELTypeFiniteExtStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_labelledCover_unitaryPELType_finiteExt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (D : DegData R (maximalIdeal R)) [Module (𝓞 E) D.toPre.X] (o : letI := H.starRing; D.toPre.OAct (𝓞 E)), Nontrivial D.toPre.X → PelOK Dm D.toPre o → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D' : DegData R' (maximalIdeal R')), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D'.toPre) ∧ Nonempty (LabCover D') := by
  first | exact @GlobalTheory.Mum.exists_labCover_of_pelOK | exact GlobalTheory.Mum.exists_labCover_of_pelOK | (intros; apply GlobalTheory.Mum.exists_labCover_of_pelOK <;> assumption)
end
end
